(defpackage #:typecase
  (:use #:cl)
  (:export #:typecase #:etypecase)
  (:shadow #:typecase #:etypecase)
  (:shadow #:member #:satisfies))

(in-package #:typecase)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Configuration
;;;

;;; Implementation specific: Given a type specifier, expand any deftypes on top
;;; level. Return two values: Head of the type specifier, and any arguments.
(defun normalize-type (type env)
  (declare (ignorable type env))
  #+clasp (core::normalize-type type)
  #-(or clasp) (error "BUG: NORMALIZE-TYPE missing implementation"))

;;; A CL type specifier. Class names that are a subtype of this specifier in the
;;; macroexpansion environment will be treated as "stable", i.e. the code
;;; generated will not account for redefinitions or subclassing.
(defvar *stable-classes*)

;;; Not customizable - convenience
(defun stable-class-p (class env)
  (subtypep class *stable-classes* env))

;;; Arrays are kind of hard to do portably this deep.
;;; This function is supposed to return a list of tclasses that represent the
;;; given specifier. The system currently assumes all you need is class checks
;;; and rank/dimension checks.
(defun array-tclasses (simple et dims env)
  (declare (ignorable simple et dims env))
  #+clasp
  (let* ((no-et (eq et '*))
         (simplep (eq simple 'simple-array))
         (uaet (if no-et et (upgraded-array-element-type et env)))
         (rank (cond ((eq dims '*) '*) ((consp dims) (length dims))
                     ((null dims) 0) (t dims)))
         (vectorp (or (eq rank '*) (= rank 1)))
         (mdp (or (eq rank '*) (/= rank 1)))
         (svnames (if no-et
                      (mapcar #'cdr core::+simple-vector-type-map+)
                      (list (core::simple-vector-type uaet))))
         (svclasses (mapcar #'find-class svnames))
         (cvnames (if no-et
                      (mapcar #'cdr core::+complex-vector-type-map+)
                      (list (core::complex-vector-type uaet))))
         (cvclasses (mapcar #'find-class cvnames))
         (smdnames (if no-et
                       (mapcar #'cdr core::+simple-mdarray-type-map+)
                       (list (core::simple-mdarray-type uaet))))
         (smdclasses (mapcar #'find-class smdnames))
         (mdnames (if no-et
                      (mapcar #'cdr core::+complex-mdarray-type-map+)
                      (list (core::complex-mdarray-type uaet))))
         (mdclasses (mapcar #'find-class mdnames))
         (test (make-dimensions dims))
         (vector-test (cond ((eq dims '*) (success))
                            ((consp dims)
                             (when (null (cdr dims))
                               (if (eq (car dims) '*)
                                   (success)
                                   test)))
                            (t nil))))
    (flet ((vector-tclass (class) (tclass class vector-test))
           (mdarray-tclass (class) (tclass class test)))
      (nconc (when vectorp
               (nconc (mapcar #'vector-tclass svclasses)
                      (unless simplep
                        (mapcar #'vector-tclass cvclasses))))
             (when mdp
               (nconc (mapcar #'mdarray-tclass smdclasses)
                      (unless simplep
                        (mapcar #'mdarray-tclass mdclasses)))))))
  #-(or clasp) (error "BUG: ARRAY-TCLASSES missing implementation"))

;;; Name of an operator "CLASSCASE" that works as following:
;;; (classcase var ((literal-class ...) body...) ... (t default-body...))
;;; Checks the DIRECT class of var against the various literal classes and
;;; executes the appropriate body, returning its values. The default body is
;;; evaluated if nothing matches.
;;; To emphasize: a subclass/generalized instance is not enough
(defvar *classcase*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Main interface
;;;

;;; Given a list of TYPECASE clauses, find any (otherwise ...)
;;; and replace with (t ...). Return other clauses, the body of the otherwise
;;; clause, and any extra (obviously unreachable) clauses as values.
(defun fix-otherwise-clause (clauses)
  (loop for (clause . more) on clauses
        if (or (eq (first clause) 'cl:otherwise)
               (eq (first clause) 'cl:t))
          return (values accum (rest clause) more)
        else collect clause into accum
        finally (return (values accum nil nil))))

(defmacro typecase (keyform &rest clauses &environment env)
  (multiple-value-bind (clauses otherwise extra)
      (fix-otherwise-clause clauses)
    (unless (null extra)
      (warn "Clauses in TYPECASE follow an otherwise clause: ~s" extra))
    (let ((keyg (gensym "TYPECASE-KEY")))
      `(let ((,keyg ,keyform))
         ,(generate-typecase keyg clauses
                             (or otherwise '(nil)) ; default default: return NIL
                             env)))))

(defmacro etypecase (keyform &rest clauses &environment env)
  (let ((keyg (gensym "ETYPECASE-KEY")))
    `(let ((,keyg ,keyform))
       ,(generate-typecase
         keyg clauses
         `((error 'type-error :datum ,keyg
                              :expected-type '(or ,@(mapcar #'car clauses))))
         env))))

(defun generate-typecase (keyg clauses otherwise env)
  (let* ((ctypes (loop for (typespec) in clauses
                       collect (canonicalize-type typespec env)))
         (tags (loop repeat (length clauses) collect (gensym "TYPECASE-RESULT")))
         (default-tag (gensym "TYPECASE-DEFAULT"))
         (block-name (gensym "TYPECASE-BLOCK"))
         (bodies (loop for (typespec . body) in clauses
                       collect `(return-from ,block-name
                                  (locally (declare (type ,typespec ,keyg))
                                    ,@body)))))
    (multiple-value-bind (tester more-tags more-bodies)
        (generate-typecase-discriminator keyg ctypes tags default-tag)
      `(block ,block-name
         (tagbody
            ,tester
            ,@(loop for tag in more-tags for body in more-bodies
                    collect tag nconc body)
            ,@(loop for tag in tags for body in bodies
                    collect tag collect body)
            ,default-tag
            (return-from ,block-name (progn ,@otherwise)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Types are, for the purposes of this system, conceived of primarily in their
;;; role in discrimination, rather than as sets.
;;; Types are broken up into two parts: Classes, and tests.
;;; A test is any part of a type that is not a class.
;;; It may be trivially true or false, or more complicated.
;;; This includes: Numeric ranges, array properties, SATISFIES, MEMBER, and
;;;  importantly, runtime class checks (to account for subclassing with classes
;;;  unknown at compile time, etc.)
;;; Because tests are at worst difficult and at most possible (SATISFIES) to
;;;  manipulate, there is no canonicalization process.
;;; Simplification is basically optional. At the moment there is none (FIXME).

;;; Abstract.
(defclass test () ())

;;; Also abstract.
(defclass junction (test)
  ((%members :initarg :members :accessor junction-members)))

(defmethod print-object ((o junction) s)
  (print-unreadable-object (o s :type t)
    (write (junction-members o) :stream s)))

(defclass conjunction (junction) ()) ; c/~ what's your function c/~
(defun conjunction (members) (make-instance 'conjunction :members members))
(defclass disjunction (junction) ())
(defun disjunction (members) (make-instance 'disjunction :members members))

(defclass negation (test)
  ((%underlying :initarg :underlying :accessor negation-underlying)))
(defun negation (underlying) (make-instance 'negation :underlying underlying))

(defclass member (test)
  ((%members :initarg :members :accessor member-members)))
(defun member (members) (make-instance 'member :members members))

(defclass satisfies (test)
  ((%fname :initarg :fname :accessor satisfies-fname)))
(defun satisfies (fname) (make-instance 'satisfies :fname fname))

(defclass cons-test (test)
  ((%car :initarg :car :accessor cons-test-car)
   (%cdr :initarg :cdr :accessor cons-test-cdr)))
(defun cons-test (car cdr)
  (make-instance 'cons-test :car car :cdr cdr))

(defclass range (test)
  ((%low :initarg :low :accessor range-low :type (or real (eql *)))
   (%low-xp :initarg :low-xp :accessor range-low-exclusive-p)
   (%high :initarg :high :accessor range-high :type (or real (eql *)))
   (%high-xp :initarg :high-xp :accessor range-high-exclusive-p)))
(defun range (low low-xp high high-xp)
  (make-instance 'range
                 :low low :low-xp low-xp :high high :high-xp high-xp))

;;; Array stuff.
(defclass dimensions (test)
  (;; A vector of dimension specifications. The CL ones, like (* 3 4).
   ;; A rank spec is normalized, e.g. 4 is now (* * * *)
   ;; They are organized by rank. For example if we had an array that
   ;; could be one dimensional, or (* 3) or (* 7), we'd have
   ;; #(() ((*)) ((* 3) (* 7)))
   (%dimses :initarg :dimses :accessor dimensions-dimensions
            :type vector)))
(defun dimensions (dimses)
  (make-instance 'dimensions :dimses dimses))
(defmethod print-object ((o dimensions) s)
  (print-unreadable-object (o s :type t)
    (write (loop for rank across (dimensions-dimensions o)
                 appending rank)
           :stream s)))

;;; A runtime class check, e.g. through class precedence lists.
(defclass runtime (test)
  ((%cname :initarg :cname :accessor runtime-cname)))
(defun runtime (cname) (make-instance 'runtime :cname cname))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Working with tests.
;;; A lot of this stuff could be made more precise. FIXME
;;;

(defgeneric tconjoin/2 (t1 t2)
  (:method ((t1 test) (t2 test)) (conjunction (list t1 t2))))
(defmethod tconjoin/2 ((t1 conjunction) (t2 conjunction))
  (conjunction (append (junction-members t1) (junction-members t2))))
(defmethod tconjoin/2 ((t1 conjunction) (t2 test))
  (apply #'test-conjoin t2 (junction-members t1)))
(defmethod tconjoin/2 ((t1 test) (t2 conjunction))
  (apply #'test-conjoin t1 (junction-members t2)))
(defmethod tconjoin/2 ((t1 test) (t2 negation))
  (tsubtract t1 (negation-underlying t2)))
(defmethod tconjoin/2 ((t1 negation) (t2 test))
  (tsubtract t2 (negation-underlying t1)))
;;; de morgan
(defmethod tconjoin/2 ((t1 negation) (t2 negation))
  (tdisjoin/2 (negation-underlying t1) (negation-underlying t2)))

;;; Given two dimension specs of the same rank, conjoin them.
;;; Return NIL if the intersection is empty.
;;; (This will always return NIL with rank 0, obviously.)
(defun conjoin-dims (d1 d2)
  (loop for dim1 in d1
        for dim2 in d2
        collect (cond ((eq dim1 '*) dim2)
                      ((eq dim2 '*) dim1)
                      (t (if (= dim1 dim2)
                             dim1
                             (return-from conjoin-dims nil))))))
;;; Given two lists of dimension specs, all of the same rank, conjoin.
;;; Result is a list of dimension specs, which can be empty.
;;; We do the dumb quadratric algorithm - conjoin them all pairwise -
;;; because I don't expect this to be a bottleneck.
;;; Doesn't work right with rank 0.
(defun conjoin-dimses (dimses1 dimses2)
  (loop for dims1 in dimses1
        nconc (loop for dims2 in dimses2
                    when (conjoin-dims dims1 dims2) collect it)))

(defmethod tconjoin/2 ((t1 dimensions) (t2 dimensions))
  (let* ((dd1 (dimensions-dimensions t1))
         (dd2 (dimensions-dimensions t2))
         (new (map 'vector #'conjoin-dimses dd1 dd2)))
    ;; Special case rank 0. Also note the vector is not length 0,
    ;; because then one argument was the empty type, which we make
    ;; sure not to make as a DIMENSIONS object.
    (when (or (aref dd1 0) (aref dd2 0))
      (setf (aref new 0) (list nil)))
    ;; Figure out if we have any nulls to cut out.
    (let ((last-rank (position-if-not #'null new :from-end t)))
      (if (null last-rank)
          ;; We have nothing.
          (failure)
          ;; Shrink the vector and make a dimensions.
          (dimensions
           (adjust-array new (1+ last-rank)))))))

(defmethod tconjoin/2 ((t1 cons-test) (t2 cons-test))
  ;; TODO?: If we canonicalized the car and cdr types as well, we
  ;; could reduce (and (cons integer) (cons cons)) to NIL and such.
  (cons-test `(and ,(cons-test-car t1) ,(cons-test-car t2))
             `(and ,(cons-test-cdr t1) ,(cons-test-cdr t2))))

(defgeneric tdisjoin/2 (t1 t2)
  (:method ((t1 test) (t2 test)) (disjunction (list t1 t2))))
(defmethod tdisjoin/2 ((t1 disjunction) (t2 disjunction))
  (disjunction (append (junction-members t1) (junction-members t2))))
(defmethod tdisjoin/2 ((t1 disjunction) (t2 test))
  (apply #'test-disjoin t2 (junction-members t1)))
(defmethod tdisjoin/2 ((t1 test) (t2 disjunction))
  (apply #'test-disjoin t1 (junction-members t2)))
;; de morgan
(defmethod tdisjoin/2 ((t1 negation) (t2 negation))
  (tconjoin/2 (negation-underlying t1) (negation-underlying t2)))

;;; Does dims1 describe a subset of dims2? Assumed same rank.
(defun dims<= (dims1 dims2)
  (loop for d1 in dims1
        for d2 in dims2
        always (or (eq d2 '*)
                   (and (not (eq d1 '*))
                        (= d1 d2)))))
;;; Given two lists of dimension specs, all of the same rank, disjoin.
(defun disjoin-dimses (dimses1 dimses2)
  (let* ((dimses1
           (loop for dims1 in dimses1
                 ;; position instead of find because with rank 0,
                 ;; elements will be nil.
                 unless (position dims1 dimses2 :test #'dims<=)
                   collect dims1))
         (dimses2
           (loop for dims2 in dimses2
                 unless (position dims2 dimses1 :test #'dims<=)
                   collect dims2)))
    (nconc dimses1 dimses2)))
(defmethod tdisjoin/2 ((t1 dimensions) (t2 dimensions))
  ;; Copy the longer vector, append in everything from the shorter.
  (let ((dd1 (dimensions-dimensions t1))
        (dd2 (dimensions-dimensions t2)))
    (when (> (length dd2) (length dd1))
      (rotatef dd1 dd2))
    (let ((new (copy-seq dd1)))
      (map-into new #'disjoin-dimses new dd2)
      (dimensions new))))

(defun test-conjoin (&rest tests)
  (cond ((null tests) (conjunction nil))
        ((null (rest tests)) (first tests))
        (t (reduce #'tconjoin/2 tests))))
(defun test-disjoin (&rest tests)
  (cond ((null tests) (disjunction nil))
        ((null (rest tests)) (first tests))
        (t (reduce #'tdisjoin/2 tests))))

(defgeneric test-negate (test)
  (:method ((test test)) (negation test)))

;;; De Morgan
(defmethod test-negate ((test conjunction))
  (apply #'test-disjoin (mapcar #'test-negate (junction-members test))))
(defmethod test-negate ((test disjunction))
  (apply #'test-conjoin (mapcar #'test-negate (junction-members test))))

;;; (AND t1 (NOT t2))
(defgeneric tsubtract (t1 t2)
  (:argument-precedence-order t2 t1)
  (:method ((t1 test) (t2 test))
    ;; Since this is called by tconjoin/2, the buck stops here:
    ;; Give up without further attempts at simplification.
    (conjunction (list t1 t2))))
;;; (and x (not (not y))) = (and x y)
(defmethod tsubtract ((t1 test) (t2 negation))
  (tconjoin/2 t1 (negation-underlying t2)))
;;; (and x (not (and y z))) = (and x (or (not y) (not z)))
;;;  = (or (and x (not y)) (and x (not z)))
;;; Note that (and x (not (and))) then reduces to (or) as we want.
(defmethod tsubtract ((t1 test) (t2 conjunction))
  (apply #'test-disjoin
         (loop for memb in (junction-members t2)
               collect (tsubtract t1 memb))))
;;; (and x (not (or y z))) = (and x (and (not y) (not z)))
;;; = (and (and x (not y)) (and x (not z)))
;;; This may not be ideal sometimes? But it'll handle (and x (and)).
(defmethod tsubtract ((t1 test) (t2 disjunction))
  (apply #'test-conjoin
         (loop for memb in (junction-members t2)
               collect (tsubtract t1 memb))))

(defmethod tsubtract ((t1 cons-test) (t2 cons-test))
  ;; TODO?: See tconjoin/2 method
  (cons-test `(and ,(cons-test-car t1) (not ,(cons-test-car t2)))
             `(and ,(cons-test-cdr t1) (not ,(cons-test-cdr t2)))))

;;; Trivial tests that often come in handy.
(defun success () (conjunction nil))
(defun failure () (disjunction nil))

;;; These obviously cannot always be correct - what if there's a monstrous
;;; SATISFIES? - but along with conjoining and disjoining tests reasonably
;;; well, this should cover a lot
(defun success-p (test)
  (and (cl:typep test 'conjunction)
       (null (junction-members test))))
(defun failure-p (test)
  (and (cl:typep test 'disjunction)
       (null (junction-members test))))

;;; deal with *s. bottom and stuff is left to later codegen, though.
;;; TODO: But we could generate canonical types now and make things smarter.
(defun make-cons-test (car cdr)
  (when (eq car '*) (setf car 't))
  (when (eq cdr '*) (setf cdr 't))
  (if (and (eq car 't) (eq cdr 't))
      (success)
      (cons-test car cdr)))

;;; Takes one argument straight from a type specifier.
(defun make-dimensions (dimspec)
  (cond ((and (integerp dimspec) (>= dimspec 0))
         (let* ((dims (make-list dimspec :initial-element '*))
                (dimses (list dims))
                (vec (make-array (1+ dimspec) :initial-element nil)))
           (setf (aref vec dimspec) dimses)
           (dimensions vec)))
        ((consp dimspec)
         (let* ((rank (length dimspec))
                (dimses (list dimspec))
                (vec (make-array (1+ rank) :initial-element nil)))
           (setf (aref vec rank) dimses)
           (dimensions vec)))
        ((null dimspec)
         (dimensions (make-array 1 :initial-element (list nil))))
        ((eq dimspec '*) (return-from make-dimensions (success)))
        (t (error "Bad dimspec ~s" dimspec))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Generate code for a test.
;;;

(defun generate-test (test var &rest code)
  `(when ,(generate-test-condition test var) ,@code))

(defgeneric generate-test-condition (test var))

(defmethod generate-test-condition ((test conjunction) var)
  `(and ,@(loop for test in (junction-members test)
                collect (generate-test-condition test var))))
(defmethod generate-test-condition ((test disjunction) var)
  `(or  ,@(loop for test in (junction-members test)
                collect (generate-test-condition test var))))

(defmethod generate-test-condition ((test negation) var)
  `(not ,(generate-test-condition (negation-underlying test) var)))

(defmethod generate-test-condition ((test member) var)
  `(or ,@(loop for member in (member-members test)
               collecting `(eql ,var ',member))))

(defmethod generate-test-condition ((test satisfies) var)
  `(,(satisfies-fname test) ,var))

(defmethod generate-test-condition ((test cons-test) var)
  ;; NOTE: Relies on car and cdr being bound beforehand.
  ;; See test-cons-involvement below.
  `(and ,@(unless (eq (cons-test-car test) 't)
            `((cl:typep car ',(cons-test-car test))))
        ,@(unless (eq (cons-test-cdr test) 't)
            `((cl:typep cdr ',(cons-test-cdr test))))))

(defmethod generate-test-condition ((test range) var)
  `(and ,@(cond ((eq (range-low test) '*) nil)
                ((range-low-exclusive-p test) `((> ,var ,(range-low test))))
                (t `((>= ,var ,(range-low test)))))
        ,@(cond ((eq (range-high test) '*) nil)
                ((range-high-exclusive-p test) `((< ,var ,(range-high test))))
                (t `((<= ,var ,(range-high test)))))))

(defmethod generate-test-condition ((test dimensions) var)
  ;; FIXME: Could probably be a lot smarter.
  (labels ((one-dimspec (spec dimsyms)
             `(and
               ,@(loop for sym in dimsyms
                       for dim in spec
                       unless (eq dim '*)
                         collect `(= ,sym ,dim))))
           (one-rank (dims rank)
             (let ((dimsyms (loop repeat rank
                                  collect (gensym "ARRAY-DIMENSION"))))
               `(let (,@(loop for j below rank
                              for sym in dimsyms
                              collect `((,sym
                                         (array-dimension ,var ,j)))))
                  (declare (ignorable ,@dimsyms))
                  (or ,@(loop for spec in dims
                               collect (one-dimspec spec dimsyms)))))))
  `(case (array-rank ,var)
     ,@(loop
         for dims across (dimensions-dimensions test)
         for i from 0
         unless (null dims)
           collect `((,i) ,(one-rank dims i))))))

(defmethod generate-test-condition ((test runtime) var)
  `(cl:typep ,var (find-class ',(runtime-cname test))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; A class with a test attached to it.
;;;
;;; In addition to being an actual class, the "class" can be the magic symbol
;;; :UNSTABLE. This indicates that the accompanying test or what ever is for
;;; classes that are unstable, i.e. will be default in classcase.
;;; Why is this useful? Because ctype else clauses (below) work for ALL classes,
;;; not just these defaults, so they can end up in real classes via dis/conjoin.
;;; But for example if we have CONS as one type and USER-CLASS as another,
;;; it would be ridiculous to check if a CONS was a USER-CLASS - it ain't.
;;; Obviously none of this is relevant if all classes are stable.
;;;

(deftype pseudoclass () '(or class (eql :unstable)))

(defclass tclass ()
  ((%class :initarg :class :accessor tclass-class :type pseudoclass)
   ;; A further test.
   (%test :initarg :test :accessor tclass-test :type test)))
(defun tclass (class test)
  (check-type class pseudoclass)
  (make-instance 'tclass :class class :test test))

(defmethod print-object ((o tclass) s)
  (print-unreadable-object (o s :type t)
    (write (tclass-class o) :stream s)
    (write-char #\Space s)
    (write (tclass-test o) :stream s)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; A canonical type (ctype) is a union and an "else" test.
;;; Elements of the union are classes with a test attached.
;;; These elements are called tclasses, for "test classes".
;;; The union contains at most one tclass for any given class.
;;; The ctype as a whole reps (or (and class1...) (and class2 ...)
;;;                               (and (not (or class1 class2...)) else...))
;;; i.e. the else clause excludes the classes, making it a sum of products.
;;; A union can be empty, in which case the else is paramount.
;;; To produce these ctypes, a type must essentially be "factored" into classes.
;;; The basic assumption that classes are completely distinct is critical.
;;;

(defclass ctype ()
  ((%tclasses :initarg :tclasses :accessor ctype-tclasses)
   (%else :initarg :else :accessor ctype-else :type test)))
(defun ctype (tclasses &optional (else (failure)))
  (make-instance 'ctype :tclasses tclasses :else else))

(defmethod print-object ((o ctype) s)
  (print-unreadable-object (o s :type t)
    (write (ctype-tclasses o) :stream s)
    (write-char #\Space s)
    (write (ctype-else o) :stream s)))

(defun ctype-top ()
  (make-instance 'ctype :tclasses nil :else (success)))

(defun ctype-bot ()
  (make-instance 'ctype :tclasses nil :else (failure)))

;;; NOTE FOR LATER: An easier way to think about All This Garbage is that if
;;; the ctypes have the same set of classes, operations can be done per-class.
;;; And a ctype can have classes added to it just by copying the ELSE in for
;;; the new tclasses. Not sure if this is more efficient however.

;;; (and (or (and c1 a1) ... (and (not (or c1...)) e1))
;;;      (or (and c2 a2) ... (and (not (or c2...)) e2)))
;;; = (or (and c1 c2 a1 a2) ... (and (not (or c1...)) (not (or c2..)) e1 e2))
;;; = (or (and c1 c2 a1 a2) ... (and (not (or (and c1 c2) ...)) e1 e2))
;;; Keep in mind that (and c1 c2) = c1 if c1 = c2, or else is empty.
;;; As such, tclasses present in both are conjoined, tclasses present in
;;; exactly one are conjoined with the other's else, and the elses conjoin.
(defun ctype-conjoin/2 (ct1 ct2)
  (let ((ct2-tclasses (copy-list (ctype-tclasses ct2)))
        (ct1-else (ctype-else ct1)) (ct2-else (ctype-else ct2)))
    (ctype
     (nconc
      (loop for tc1 in (ctype-tclasses ct1)
            for class = (tclass-class tc1)
            for test1 = (tclass-test tc1)
            for tc2 = (find class ct2-tclasses
                            :test #'eq :key #'tclass-class)
            ;; If both ctypes have the tclass, conjoin them in the result.
            ;; Otherwise, conjoin the lone tclass with the other's else.
            if tc2
              do (setf ct2-tclasses (delete tc2 ct2-tclasses :test #'eq))
              and collect (tclass class (test-conjoin test1
                                                      (tclass-test tc2)))
            else collect (tclass class (test-conjoin test1 ct2-else)))
      ;; Anything left in ct2-tclasses is unpaired, so conjoin it with
      ;; ct1's else.
      (loop for tc2 in ct2-tclasses
            collect (tclass (tclass-class tc2)
                            (test-conjoin (tclass-test tc2) ct1-else))))
     ;; The else of the new type is just the intersection of the elses.
     (test-conjoin ct1-else ct2-else))))

(defun ctype-conjoin (ctypes)
  (cond ((null ctypes) (ctype-top))
        ((null (rest ctypes)) (first ctypes))
        (t (reduce #'ctype-conjoin/2 ctypes))))

;;; I'm going to say, without bothering to work out the algebra and prove
;;; it, that this is just dual to conjunction.
(defun ctype-disjoin/2 (ct1 ct2)
  (let ((ct2-tclasses (copy-list (ctype-tclasses ct2)))
        (ct1-else (ctype-else ct1)) (ct2-else (ctype-else ct2)))
    (ctype
     (nconc
      (loop for tc1 in (ctype-tclasses ct1)
            for class = (tclass-class tc1)
            for test1 = (tclass-test tc1)
            for tc2 = (find class ct2-tclasses
                            :test #'eq :key #'tclass-class)
            if tc2
              do (setf ct2-tclasses (delete tc2 ct2-tclasses :test #'eq))
              and collect (tclass class (test-disjoin test1
                                                      (tclass-test tc2)))
            else collect (tclass class (test-disjoin test1 ct2-else)))
      (loop for tc2 in ct2-tclasses
            collect (tclass (tclass-class tc2)
                            (test-disjoin (tclass-test tc2) ct1-else))))
     (test-disjoin ct1-else ct2-else))))

(defun ctype-disjoin (ctypes)
  (cond ((null ctypes) (ctype-bot))
        ((null (rest ctypes)) (first ctypes))
        (t (reduce #'ctype-disjoin/2 ctypes))))

;;; Negation is a little more confusing.
;;; By De Morgan's laws, negation of a union will be a conjunction of the
;;; negations of the union's elements.
;;; So in our case, that means we have a conjunction of
;;;  (not (and c_n test_n))s with (not (and (not (or c_n...)) else)).
;;; Applying De Morgan again to this latter we have (or c_n... (not else)).
;;; The former are (or (not c_n) (not test_n)), which we can expand to
;;;  (or (not c_n) (and c_n (not test_n))). IMPORTANT
;;; We need to carry out this conjunction in such a way that we get a
;;;  properly factored type again.
;;; The conjunction of any two of the former is, by distributivity,
;;;  (or (and (not c_m) (not c_n)) (and (not c_m) (and c_n (not test_n)))
;;;      (and (not c_n) (and c_m (not test_m)))
;;;      (and (and c_m (not test_m)) (and c_n (not test_n))))
;;; Since (and c_n c_m) is empty, we can eliminate the final clause,
;;;  and (and (not c_m) (and c_n (not test_n))) = (and c_n (not test_n)).
;;; (and (not c_m) (not c_n)) De Morgans to (not (or c_m c_n)).
;;; So the whole thing is (or (and c_m (not test_m)) (and c_n (not test_n))
;;;                           (not (or c_m c_n))).
;;; Applying this to all the former (non-else) clauses, we get the canonical
;;; (or (and c_n (not test_n)) ... (not (or c_n...)))
;;; Now we need to conjoin this with the else clause, (or c_n... (not else))
;;; This canonizes to (or (and c_n) ...
;;;                       (and (not (or c_n...)) (not else))),
;;;  so we can work classwise.
;;; Each c_n clause combines to get (and c_n (not test_n)),
;;; and (and (not (or c_n...)) (and (not (or c_n...)) (not else)))
;;; obviously reduces to (and (not (or c_n...)) (not else)).
;;;
;;; This is all way too much algebra to tell us we can just negate by
;;;  class. Fuck.
(defun ctype-negate (ctype)
  (ctype
   (loop for tc in (ctype-tclasses ctype)
         collect (tclass (tclass-class tc)
                         (test-negate (tclass-test tc))))
   (test-negate (ctype-else ctype))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Given a Lisp typespec, return an object representing a "canonicalized" type:
;;; independent of the environment, and first based on class discrimination.
;;; FIXME: We forgive some bad types like (t foo...)
(defun canonicalize-type (typespec env)
  (flet ((recur (ts) (canonicalize-type ts env)))
    (multiple-value-bind (head args) (normalize-type typespec env)
      (case head
        ((t)   (ctype-top))
        ((nil) (ctype-bot))
        ((and) (ctype-conjoin (mapcar #'recur args)))
        ((or)  (ctype-disjoin (mapcar #'recur args)))
        ((not) (ctype-negate (recur (first args))))
        ((eql) (make-member-ctype (list (first args)) env))
        ((cons) (destructuring-bind (&optional (car '*) (cdr '*)) args
                  (make-cons-ctype car cdr env)))
        ((array simple-array)
         (destructuring-bind (&optional (et '*) (dims '*)) args
           (make-array-ctype head et dims env)))
        ((short-float long-float
          single-float double-float
          float integer rational real)
         (destructuring-bind (&optional (low '*) (high '*)) args
           (make-range-ctype head low high env)))
        ((satisfies) (ctype nil (satisfies (first args))))
        ((cl:member) (make-member-ctype args env))
        ;; TODO: cons, numbers, etc
        (t
         (unless (null args)
           (error "Unknown complex type: ~s" typespec))
         (make-name-ctype head env))))))

;;; Given what's assumed to be a class name, return a ctype for it.
;;; Depending on the class, this may either be an actual class test, or some
;;; slower runtime thing. The latter is necessary to allow for redefinitions and
;;; subclassing.
;;; Also if the name is unknown it's the runtime thing.
(defun make-name-ctype (name env)
  (let ((class (find-class name nil env)))
    (if (and class (stable-class-p class env))
        (ctype (list (tclass class (success))))
        (ctype (list (tclass :unstable (runtime name)))))))

;;; make a canonical-test for a member type.
;;; this will still be broken up by classes.
(defun make-member-ctype (members env)
  ;; Make an alist (class ...elements)
  (loop with alist = nil
        for elt in members
        for pre-class = (class-of elt)
        for class = (if (stable-class-p pre-class env)
                        pre-class
                        :unstable)
        for entry = (assoc class alist :test #'eq)
        when (null entry) do (push (list class elt) alist)
          else do (push elt (rest entry))
        finally (return
                  (ctype
                   (loop for (class . elems) in alist
                         collect (tclass class (member elems)))))))

(defun make-cons-ctype (car cdr env)
  (let ((test (make-cons-test car cdr))
        (class (find-class 'cons t env)))
    (if (stable-class-p class env)
        (ctype (list (tclass class test)))
        (ctype (list (tclass :unstable
                             (test-conjoin (runtime 'cons) test)))))))

;;; numeric ranges.
;;: FIXME: We assume all subtypes of REAL are stable, and that fixnum, bignum,
;;; and any etc-float that are actually distinct are all classes.
;;; Writing this is really annoying otherwise.
(defun float-class (name env)
  ;; Ideally, all these subtypeps should reduce to constants.
  (macrolet ((floatcase (name &rest possibles)
               `(cond ,@(loop for possible in possibles
                              collect `((subtypep ',name ',possible env)
                                        (find-class ',possible t env)))
                      (t (find-class ',name t env)))))
    (ecase name
      ((short-float) (floatcase short-float single-float))
      ((long-float) (floatcase long-float single-float double-float))
      ((double-float) (floatcase double-float single-float))
      ((single-float) (floatcase single-float)))))
;;; Technically we could be smarter with this, but also I don't care.
(defun float-classes (env)
  (delete-duplicates (loop for name in '(short-float long-float
                                         single-float double-float)
                           collect (float-class name env))
                     :test #'eq))
(defun float-tclasses (test env)
  (mapcar (lambda (class) (tclass class test)) (float-classes env)))
;;; Divvy up into fixnum and bignum.
(defun integer-range-tclasses (test env)
  (let ((low (range-low test)) (low-xp (range-low-exclusive-p test))
        (high (range-high test)) (high-xp (range-high-exclusive-p test)))
    ;; Convert to inclusive range for simplicity's sake.
    (when low-xp (incf low))
    (when high-xp (decf high))
    ;; Divvy
    (multiple-value-bind (bignum-low fixnum-low)
        (cond ((eq low '*) (values low low))
              ((< low most-negative-fixnum) (values low '*))
              ((= low most-negative-fixnum) (values nil '*))
              ((<= low most-positive-fixnum) (values nil low))
              (t (values nil nil)))
      (multiple-value-bind (bignum-high fixnum-high)
          (cond ((eq high '*) (values high high))
                ((> high most-positive-fixnum) (values high '*))
                ((= high most-positive-fixnum) (values nil '*))
                ((>= high most-negative-fixnum) (values nil high))
                (t (values nil nil)))
        (let ((bignum-test-low
                (if (null bignum-low)
                    (failure)
                    (range bignum-low nil (1- most-negative-fixnum) nil)))
              (bignum-test-high
                (if (null bignum-high)
                    (failure)
                    (range (1+ most-positive-fixnum) nil bignum-high nil)))
              (fixnum-test
                (if (and fixnum-low fixnum-high)
                    (range fixnum-low nil fixnum-high nil)
                    (failure))))
          (list (tclass (find-class 'fixnum t env) fixnum-test)
                (tclass (find-class 'bignum t env)
                        (test-disjoin bignum-test-low bignum-test-high))))))))
(defun make-range-ctype (cname low high env)
  (let* ((low-xp (consp low))
         (high-xp (consp high))
         (test (range (if low-xp (car low) low) low-xp
                      (if high-xp (car high) high) high-xp)))
    (ctype
     (ecase cname
       ((short-float single-float double-float long-float)
        (list (tclass (float-class cname env) test)))
       ((float) (float-tclasses test env))
       ((rational)
        (list* (tclass (find-class 'ratio t env) test)
               (integer-range-tclasses test env)))
       ((integer) (integer-range-tclasses test env))
       ((real)
        (nconc (float-tclasses test env)
               (integer-range-tclasses test env)
               (list (tclass (find-class 'ratio t env) test))))))))

(defun make-array-ctype (simple et dims env)
  (ctype (array-tclasses simple et dims env) (failure)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Given a set (list) of ctypes, return two values.
;;; The first value is a list of lists of tclasses. These lists are the lists
;;; of tclasses from the ctypes, in the same order, except that they've been
;;; augmented so that all classes in the ctype set have a tclass.
;;; The second value is this list of all classes.
;;; So for example, if we have #<ctype (#<tclass #<class FOO> test1>) else1>
;;;  and #<ctype (#<tclass #<class BAR> test2>) else2>,
;;; ((#<tclass #<class FOO> test1> #<tclass #<class BAR> else1>)
;;;  (#<tclass #<class FOO> else2> #<tclass #<class BAR> test2>))
;;; would be the first return value, though the classes may not be ordered.
;;; This makes the code generation easier. Not the most efficient way though.

(defun standardize-ctypes (ctypes)
  (let ((classes (delete-duplicates
                  (loop for ctype in ctypes
                        nconc (mapcar #'tclass-class (ctype-tclasses ctype)))
                  :test #'eq)))
    (values
     (loop for ctype in ctypes
           for tclasses = (ctype-tclasses ctype)
           for else = (ctype-else ctype)
           for ctype-classes = (mapcar #'tclass-class tclasses)
           for new-classes = (set-difference classes ctype-classes :test #'eq)
           for new-tclasses = (loop for class in new-classes
                                    collect (tclass class else))
           collect (nconc new-tclasses tclasses))
     classes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Given a variable, a list of ctypes, and a list of the same
;;; length of GO tags to jump to correspondingly, return a testing form.
;;; The testing form will at runtime perform each test in turn (or equivalent)
;;; on the variable, and jump to the corresponding tag if the test succeeds.
;;; The tests are assumed to be comprehensive - no type left out.
;;;
;;; FIXME: The current design does not have multiple classes reaching the same
;;; destination in a way CLASSCASE can discern, so it can't merge ranges and
;;; stuff like that.
;;;
(defun generate-typecase-discriminator (var ctypes tags default-tag)
  (multiple-value-bind (discs all-classes)
      (standardize-ctypes ctypes)
    (let* (;; :UNSTABLE is special.
           ;; FIXME: This is all pretty inefficient.
           (unstablep (find :unstable all-classes))
           (real-all-classes (delete :unstable all-classes :test #'eq))
           ;; The CDRs of the alist pairs will be (test . tag)s in reverse order
           ;; of their eventual execution.
           (alist (mapcar #'list real-all-classes))
           ;; Another (test . tag) list in reverse order.
           (default nil))
      ;; Go through the discs putting in the tests.
      (loop for disc in discs
            for tag in tags
            for ctype in ctypes
            for else = (ctype-else ctype)
            do (loop for pair in alist
                     for class = (car pair)
                     for test = (tclass-test
                                 (or (find class disc :test #'eq :key #'tclass-class)
                                     (error "BUG: Wtf")))
                     do (push (cons test tag) (cdr pair)))
               ;; If there's an :UNSTABLE clause pull it out to the default,
               ;; along with the else.
               (when unstablep
                 (push (cons (tclass-test
                              (or (find :unstable disc :test #'eq :key #'tclass-class)
                                  (error "BUG: Wtf2")))
                             tag)
                       default))
               (push (cons else tag) default))
      ;; Reverse and consolidate the test-tags.
      ;; A consolidated thing is (tag . test-tags), meaning to try the test-tags,
      ;; and then if none of them pass, go to tag. This makes mergers easier and stuff.
      (loop for pair in alist
            do (setf (cdr pair)
                     (consolidate-test-tags (nreverse (cdr pair)) default-tag)))
      (setf default (consolidate-test-tags (nreverse default) default-tag))
      ;; If multiple classes do no tests and go to the same tag, merge their clauses.
      ;; TODO: Could be possible to recognize shared suffixes and stuff too.
      (let ((alist
              (loop with simple = nil
                    for (class . (tag . test-tags)) in alist
                    if (null test-tags)
                      do (let ((pair (find tag simple :test #'eq :key #'second)))
                           (if pair
                               (push class (car pair))
                               (push (list (list class) tag) simple)))
                    else collect (list* (list class) tag test-tags) into other
                    finally (return (nconc simple other)))))
        ;; Now just build the form.
        `(,*classcase* ,var
           ,@(loop for (classes tag . test-tags) in alist
                   collect `(,classes ,@(generate-tests var test-tags) (go ,tag)))
           (t ,@(generate-tests var (cdr default)) (go ,(car default))))))))

;;; Given a list (test . tag) in order, return (tag . (test . tag)*).
;;; Remove any auto-fail tests, and stop early if there's a success.
(defun consolidate-test-tags (test-tags default-tag)
  (loop for pair in test-tags
        for (test . tag) = pair
        ;; Potentially we could be cleverer about issuing warnings for redundant tests?
        ;; That is, any after a success.
        when (success-p test)
          return (cons tag new-test-tags)
        unless (failure-p test)
          collect pair into new-test-tags
        finally (return (cons default-tag new-test-tags))))
;;; Given a list (test . tag) in order, generate code to carry out the tests.
;;; The code will be a list of forms.
(defun generate-tests (var test-tags)
  ;; Pick off special cases.
  ;; if there are no test-tags, do nothing
  (when (null test-tags) (return-from generate-tests nil))
  ;; if any tests are cons tests, grab the car and cdr for them all to share
  (let ((bindings nil)
        (cons-testing (test-list-cons-involvement (mapcar #'car test-tags))))
    (ecase cons-testing
      ((nil))
      ((:car) (push `(car (car ,var)) bindings))
      ((:cdr) (push `(cdr (cdr ,var)) bindings))
      ((:car-and-cdr)
       (push `(car (car ,var)) bindings)
       (push `(cdr (cdr ,var)) bindings)))
    ;; Actually generate tests.
    `((let (,@bindings)
        ,@(loop for (test . tag) in test-tags
                collect (generate-test test var `(go ,tag)))))))

;;; Given a list of tests, return a symbol to indicate what they grab
;;; out of conses. NIL means nothing, and then there's :car, :cdr, or :car-and-cdr.
(defun test-list-cons-involvement (test-list)
  (loop with result = nil
        for test in test-list
        for involvement = (test-cons-involvement test)
        do (setf result (disjoin-involvement result involvement))
        finally (return result)))

(defun disjoin-involvement (i1 i2)
  (ecase i1
    ((:car-and-cdr) i1)
    ((:car) (ecase i2
              ((nil) i1)
              ((:car :car-and-cdr) i2)
              ((:cdr) :car-and-cdr)))
    ((:cdr) (ecase i2
              ((nil) i1)
              ((:cdr :car-and-cdr) i2)
              ((:car) :car-and-cdr)))
    ((nil) i2)))

;;; Get the cons involvement for one test.
(defgeneric test-cons-involvement (test)
  (:method ((test test)) nil))

(defmethod test-cons-involvement ((test cons-test))
  (let ((car (if (eq (cons-test-car test) 't) nil :car))
        (cdr (if (eq (cons-test-cdr test) 't) nil :cdr)))
    (disjoin-involvement car cdr)))

(defmethod test-cons-involvement ((test negation))
  (test-cons-involvement (negation-underlying test)))
(defmethod test-cons-involvement ((test junction))
  (test-list-cons-involvement (junction-members test)))
