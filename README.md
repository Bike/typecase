This is a semi portable implementation of the CL macros typecase, etypecase, and ctypecase.

It is based on the premise that there is a fast way to check the direct class of an object against a variety of options known at compile time, all at once. This system expects a macro to accomplish this, as described in the file. The premise is true in SICL (https://github.com/robert-strandh/SICL) and possibly other implementations; failing other options, you could use `class-of` and `case`.

Essentially, all types are divided up into exclusive subtypes by class. For example, the type `(or cons (satisfies foo) (vector * 7))` might become, roughly, `(or (and cons t) (and vector (vector * 7)) (and (not (or cons vector)) (satisfies foo)))`. A `typecase` then reduces to a `classcase` which checks the class first and then only runs further checks if required.

Because this `classcase` works with _direct_ classes, it cannot handle inheritance. That is, if `foo` is a (strict) subclass of `bar`, an entry for only `bar` will not be chosen for a `foo` instance. In order to work correctly, the tyepcase must do a more complicated runtime check, such as checking the class precedence list of the direct class of the objecting being tested. This system handles this by requiring a type for "stable classes", that is, classes that cannot be subclassed or redefined, and putting only these in the classcase; others go through a runtime check. (The check is currently a `cl:typep` call, but this could potentially be improved.)

Some aspects of the CL typecase are difficult to work with portably. To work with a given implementation, the functions `normalize-type` and `array-tclasses` must be defined. The first is given a type specifier and environment, and returns the type specifier free of toplevel deftypes, and split into two values, the head and the rest (so (cons * integer) would return as cons, (* integer)). `array-tclasses` handles array type specifiers, because exactly which array types correspond to classes could differ a lot between implementations.

Here is an example of how to use the system:

```
;;; Example code from a cl:format implementation.
(let (;; Bind the name of the classcase macro.
      (typecase:*classcase* 'classcase)
      ;; Structures and standard objects obviously have subclassable classes.
      ;; We say stream does because of the gray streams extension.
      (typecase:*stable-classes* '(not (or structure-object standard-object stream))))
  (macroexpand-1 '(typecase:etypecase destination
                   (null
                    (with-output-to-string (stream)
                      (formatter-aux stream control-string format-arguments)))
                   (string
                    (with-output-to-string (stream destination)
                      (formatter-aux stream control-string format-arguments)))
                   ((member t)
                    (formatter-aux *standard-output* control-string format-arguments)
                    nil)
                   (stream
                    (formatter-aux destination control-string format-arguments)
                    nil))))
```

This might result in

```
(LET ((#:ETYPECASE-KEY398419 DESTINATION))
  (BLOCK #:TYPECASE-BLOCK398459
    (TAGBODY
      (CLASSCASE #:ETYPECASE-KEY398419
       ((#<The BUILT-IN-CLASS CORE:STR-WNS>
         #<The BUILT-IN-CLASS CORE:SIMPLE-CHARACTER-STRING>
         #<The BUILT-IN-CLASS CORE:STR8NS>
         #<The BUILT-IN-CLASS SIMPLE-BASE-STRING>)
        (GO #:TYPECASE-RESULT398455))
       ((#<The BUILT-IN-CLASS NULL>)
        (WHEN (OR (EQL #:ETYPECASE-KEY398419 'NIL))
          (GO #:TYPECASE-RESULT398454))
        (GO #:TYPECASE-DEFAULT398458))
       ((#<The BUILT-IN-CLASS SYMBOL>)
        (WHEN (OR (EQL #:ETYPECASE-KEY398419 'T)) (GO #:TYPECASE-RESULT398456))
        (GO #:TYPECASE-DEFAULT398458))
       (T
        (WHEN (TYPEP #:ETYPECASE-KEY398419 (FIND-CLASS 'STREAM))
          (GO #:TYPECASE-RESULT398457))
        (GO #:TYPECASE-DEFAULT398458)))
     #:TYPECASE-RESULT398454
      (RETURN-FROM #:TYPECASE-BLOCK398459
        (LOCALLY
         (DECLARE (TYPE NULL #:ETYPECASE-KEY398419))
         (WITH-OUTPUT-TO-STRING (STREAM)
           (FORMATTER-AUX STREAM CONTROL-STRING FORMAT-ARGUMENTS))))
     #:TYPECASE-RESULT398455
      (RETURN-FROM #:TYPECASE-BLOCK398459
        (LOCALLY
         (DECLARE (TYPE STRING #:ETYPECASE-KEY398419))
         (WITH-OUTPUT-TO-STRING (STREAM DESTINATION)
           (FORMATTER-AUX STREAM CONTROL-STRING FORMAT-ARGUMENTS))))
     #:TYPECASE-RESULT398456
      (RETURN-FROM #:TYPECASE-BLOCK398459
        (LOCALLY
         (DECLARE (TYPE (COMMON-LISP:MEMBER T) #:ETYPECASE-KEY398419))
         (FORMATTER-AUX *STANDARD-OUTPUT* CONTROL-STRING FORMAT-ARGUMENTS)
         NIL))
     #:TYPECASE-RESULT398457
      (RETURN-FROM #:TYPECASE-BLOCK398459
        (LOCALLY
         (DECLARE (TYPE STREAM #:ETYPECASE-KEY398419))
         (FORMATTER-AUX DESTINATION CONTROL-STRING FORMAT-ARGUMENTS)
         NIL))
     #:TYPECASE-DEFAULT398458
      (RETURN-FROM #:TYPECASE-BLOCK398459
        (PROGN
         (ERROR 'TYPE-ERROR
                :DATUM
                #:ETYPECASE-KEY398419
                :EXPECTED-TYPE
                '(OR NULL STRING (COMMON-LISP:MEMBER T) STREAM)))))))
```
