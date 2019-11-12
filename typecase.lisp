(defpackage #:typecase
  (:use #:cl)
  (:export #:typecase)
  (:shadow #:typecase)
  (:shadow #:member #:satisfies))

(in-package #:typecase)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Configuration
;;;

;;; Implementation specific: Given a type specifier, expand any deftypes on top
;;; level. Return two values: Head of the type specifier, and any arguments.
(defun normalize-type (type env)
  (declare #+clasp (ignore env))
  #+clasp (core::normalize-type type)
  #-(or clasp) (error "BUG: NORMALIZE-TYPE missing implementation"))

;;; A CL type specifier. Class names that are a subtype of this specifier in the
;;; macroexpansion environment will be treated as "stable", i.e. the code
;;; generated will not account for redefinitions or subclassing.
(defvar *stable-classes*)

;;; Not customizable - convenience
(defun stable-class-p (class env)
  (subtypep class *stable-classes* env))

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
    (generate-typecase keyform clauses
                       (or otherwise '(nil)) ; default default: return NIL
                       env)))

(defun generate-typecase (keyform clauses otherwise env)
  (let* ((ctypes (loop for (typespec) in clauses
                       collect (canonicalize-type typespec env)))
         (tags (loop repeat (length clauses) collect (gensym "TYPECASE-RESULT")))
         (default-tag (gensym "TYPECASE-DEFAULT"))
         (block-name (gensym "TYPECASE-BLOCK"))
         (keyg (gensym "TYPECASE-KEY"))
         (bodies (loop for (typespec . body) in clauses
                       collect `(return-from ,block-name
                                  (locally (declare (type ,typespec ,keyg))
                                    ,@body)))))
    (multiple-value-bind (tester more-tags more-bodies)
        (generate-typecase-discriminator keyg ctypes tags default-tag)
      `(let ((,keyg ,keyform))
         (block ,block-name
           (tagbody
              ,tester
              ,@(loop for tag in more-tags for body in more-bodies
                      collect tag nconc body)
              ,@(loop for tag in tags for body in bodies
                      collect tag collect body)
              ,default-tag
              (return-from ,block-name (progn ,@otherwise))))))))

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

;;; A runtime class check, e.g. through class precedence lists.
(defclass runtime (test)
  ((%cname :initarg :cname :accessor runtime-cname)))
(defun runtime (cname) (make-instance 'runtime :cname cname))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; These could be improved. FIXME
;;;

(defun test-conjoin (&rest tests) (conjunction tests))
(defun test-disjoin (&rest tests) (disjunction tests))
(defun test-negate (test) (negation test))

;;; Compare tests to see if they're definitely identical.
;;; Return two values like subtypep.
(defgeneric test= (test1 test2)
  (:method ((t1 test) (t2 test))
    (values nil nil)))
(defmethod test= ((t1 junction) (t2 junction))
  (let ((t1m (junction-members t1)) (t2m (junction-members t2)))
    (if (and (= (length t1m) (length t2m)))
        (let ((t2m (copy-list t2m)))
          ;; Find elementwise matches.
          (loop for t1mem in t1m
                for t2mem = (find t1mem t2m :test #'test=)
                if t2mem
                  do (setf t2m (delete t2mem t2m :test #'eq))
                else ;; no exact match - give up
                do (return-from test= (values nil nil)))
          ;; Everything had a match.
          (values t t))
        (values nil nil))))
(defmethod test= ((t1 negation) (t2 negation))
  (test= (negation-underlying t1) (negation-underlying t2)))
(defmethod test= ((t1 member) (t2 member))
  ;; Check if the members are identical.
  (if (null (set-exclusive-or (member-members t1) (member-members t2)))
      (values t t)
      (values nil t)))
(defmethod test= ((t1 satisfies) (t2 satisfies))
  (if (eq (satisfies-fname t1) (satisfies-fname t2))
      (values t t)
      (values nil nil)))
(defmethod test= ((t1 runtime) (t2 runtime))
  (if (eq (runtime-cname t1) (runtime-cname t2))
      (values t t)
      (values nil nil)))

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
(defun ctype (tclasses else)
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
        ((satisfies) (ctype nil (satisfies (first args))))
        ((member) (make-member-ctype args env))
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
        (ctype (list (tclass class (success))) (failure))
        (ctype (list (tclass :unstable (runtime name))) (failure)))))

;;; make a canonical-test for a member type.
;;; this will still be broken up by classes.
(defun make-member-ctype (members env)
  ;; Make an alist (class ...elements)
  (loop with alist = nil
        for elt in members
        for pre-class = (class-of elt)
        for class = (if (stable-class-p pre-class env)
                        class
                        :unstable)
        for entry = (assoc class alist :test #'eq)
        when (null entry) do (push (list class elt) alist)
          else do (push elt (rest entry))
        finally (return
                  (ctype
                   (loop for (class . elems) in alist
                         collect (tclass class (member elems)))
                   (failure)))))

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
                 (push (cons (or (cdr (assoc :unstable disc :test #'eq))
                                 (error "BUG: Wtf2"))
                             tag)
                       default))
               (push (cons else tag) default))
      ;; Now just build the form.
      `(,*classcase* ,var
        ,@(loop for (class . test-tags) in alist
                collect `((,class) ,@(generate-tests var (nreverse test-tags) default-tag)))
        (t ,@(generate-tests var (nreverse default) default-tag))))))

;;; Given a list (test . tag) in order, generate code to carry out the tests.
;;; The code will be a list of forms.
(defun generate-tests (var test-tags default-tag)
  (nconc
   (loop for (test . tag) in test-tags
         ;;; Potentially we could be cleverer about issuing warnings for redundant tests?
         when (success-p test)
           collect `(go ,tag) into forms
           and do (return-from generate-tests forms)
         unless (failure-p test)
           collect (generate-test test var `(go ,tag)) into forms
         finally (return forms))
   (list `(go ,default-tag))))
