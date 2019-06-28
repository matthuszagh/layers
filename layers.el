;;; layers.el --- Main file -*-lexical-binding: t;-*-
;;
;; terminology:
;;
;; + Each call to the `layer-def' macro is an instance.
;; + The layer name is the identifier that immediately follows
;;   `layer-def'.
;; + Each instance contains one or more stages. A stage is indicated by
;;   a keyword. The only required keyword is `:init'. All others are
;;   optional.
;; + A stage includes the stage keyword and the body of the stage. The
;;   body consists of 1 or more s-expressions that (if evaluated) are
;;   evaluated as top-level sexps. I refer to these top-level sexps as
;;   forms. :depends and :types are exceptions: they are simple lists
;;   (except they shouldn't be quoted) and do not support embedded
;;   lists.
;; + An element is any unit with an instance. This can be the layer
;;   name, a keyword, a form, etc.
;; + I use content to describe collections of elements that do not fit
;;   into one of the other categories.
;;
;;; Code:

(require 'ht)
(require 'dash)

(defgroup layers nil
  "Simplify dependency management between collections of
packages."
  :group 'startup)

(defcustom layers-keywords
  '(:depends
    :types
    ;; :preinit
    :init
    :postinit
    :func
    :config)
  "doc"
  :type '(repeat symbol)
  :group 'layers)

(defsubst layers-error (msg)
  "Append layers: to the error message, so the error can be
tracked to this package."
  (error "layers: %s" msg))

(defvar layers--layer-names '())
(defvar layers--unparsed-layers '())
(defvar layers--layer-deps '())
(defvar layers--layer-types '())

(defvar layers-hash (ht))

(defun declare-layers (layers)
  "Declare list of LAYERS to use."
  (if (not (listp layers))
      (layers-error "`declare-layers' takes a list.")
    (setq layers--layer-names layers)
    (setq layers--unparsed-layers layers)
    (dolist (layer-name layers)
      (ht-set! layers-hash layer-name (ht)))))

(defmacro layers//eval-after-load-all (features body)
  "TODO improve to be able to evaluate dependencies in any order."
  (if (null features)
      body
    `(eval-after-load (quote ,(car features))
       (quote (layers//eval-after-load-all ,(cdr features) ,body)))))

(defun layers-handler/:init (hash body name)
  "Schedule evaluation for :init stage's BODY. HASH is the stage
hash map and NAME is the layer name. Evaluate all applicable
forms now, or specify their future evaluation dependencies unmet."
  (unless body
    (layers-error (format (concat "mandatory :init stage ommitted "
                                  "for layer %s") name)))
  (let ((deps (ht-get hash :depends)))
    (if deps
        (layers//eval-after-load-all
         (mapc (lambda (dep)
                 (make-symbol "layers-" dep)) deps)
         (progn (mapc 'eval body)
                (provide (make-symbol (concat "layers-" name))))))
    (mapc 'eval body)
    (provide (make-symbol (concat "layers-" name)))))

(defun layers/postinit-priority-exists? (type-hash-val)
  "Return t if any entries in a postinit for a given type have a
priority set. TYPE-HASH-VAL is the value of the type-hash."
  (dolist (entry type-hash-val)
    (if (car entry)
        t)))

(defun layers/schedule-postinit-forms (type val)
  "Schedule postinit forms. TYPE is the :postinit entry type and
val is a list whose first element is the priority and whose
second is the body of the :postinit entry."
  (if (string= type "nil-type")
      (dolist (elem val)
        (let ((body (cadr elem)))
          (dolist (form body)
            (with-eval-after-load '-layers--init-complete
              (eval form)))))
    (let ((priority-exists? (layers/postinit-priority-exists? val)))
      (dolist (elem val)
        (let ((priority (car elem))
              (body (cadr elem)))
          (if (and priority-exists?
                   priority)
              (dolist (form body)
                (with-eval-after-load '-layers--init-complete
                  (eval form)))
            (dolist (form body)
              (with-eval-after-load '-layers--init-complete
                (eval form)))))))))

(defun layers/add-postinit-form-to-types-hash (form types-hash)
  "TYPES-HASH holds a map of each type associated with a list,
where the first element of the list is the priority (t or nil)
and the second element is the body of the FORM. FORM is a single
entry in the postinit. It has the format

(:layer layer-name &optional type priority
 (body...))

Where body consists of 1 or more sexps.
"
  (unless (keywordp (car form))
    (layers-error (concat "all postinit forms must specify a layer using "
                          "the `:layer' keyword.")))
  (let ((layer (cadr form))
        (rest (cddr form))
        (type "nil-type")
        (priority nil))
    (if (ht-get layers-hash layer) ; filter unused layers
        (progn
          (unless (consp (car rest)) ; check if type set
            (setq type (car rest))
            (setq rest (cdr rest))
            (unless (consp (cadr rest)) ; check if priority set
              (setq priority (cadr rest))
              (setq rest (cddr rest))))
          (unless (ht-get types-hash type)
            (ht-set! types-hash type '()))
          (ht-set! types-hash type
                   (append (ht-get types-hash type) (list `(,priority ,rest))))))))

(defun layers-handler/:postinit (hash body name)
  "Handles processing of the :postinit body. HASH is the hash map
for the current layer and BODY is :postinit's wrapped
body. Handle processing by first constructing a `types-hash'
where the key is the type of each form ('nil-type' for forms
without a type) and value is a list whose first element is the
priority (t or nil) and whose second element is wrapped body of
the form."
  (let ((types-hash (ht ("nil-type" '()))))
    (dolist (form body)
      (layers/add-postinit-form-to-types-hash form types-hash))
    (ht-map 'layers/schedule-postinit-forms types-hash)))

(defun layers-handler/:func (_hash body _name)
  ""
  (with-eval-after-load '-layers--init-complete
    (mapc 'eval body)))

(defun layers-handler/:config (_hash body _name)
  ""
  (with-eval-after-load '-layers--init-complete
    (mapc 'eval body)))

(defun layers/add-stage-to-hash (name stage)
  "Take a single, wrapped stage and add it to the global
`layers-hash'. NAME is the layer name and STAGE is the stage to
add."
  (let ((key (car stage))
        (val (cdr stage)))
    (ht-set! (ht-get layers-hash name) key val)))

(defmacro layers//handle-keyword (hash key name)
  ""
  (let ((val `(ht-get ,hash ,key)))
    `(,(intern (concat "layers-handler/"
                       (symbol-name key))) ,hash ,val ,name)))

(defun layers/process-keywords-from-hash (name)
  "Pass all keyword arguments for layer NAME to their respective
handlers. Ignore any undeclared layers."
  (setq layers--unparsed-layers (-remove-item name layers--unparsed-layers))
  (unless layers--unparsed-layers
    (provide '-layers--init-complete))
  (let ((layer-hash (ht-get layers-hash name)))
    (layers//handle-keyword layer-hash :init (symbol-name name))
    (layers//handle-keyword layer-hash :postinit (symbol-name name))
    (layers//handle-keyword layer-hash :func (symbol-name name))
    (layers//handle-keyword layer-hash :config (symbol-name name))))

(defun layers/trim-trailing-keywords (content)
  "Returns the full body of a stage by getting rid of everything
from the next keyword down. CONTENT has the form:

(expr1)
(expr2)
...
(:keyword)
(more content...)

In the example above, `layers/trim-trailing-keywords' would return

((expr1)
 (expr2)
 ...)

In other words, it returns just the body of the stage but wraps
it in a list. This would be true even if the body contained a
single form.
"
  (let ((body))
    (unless (keywordp (car content))
      (setq body (append body (list (car content))))
      (setq content (cdr content))
      (while (and (car content)
                  (not (keywordp (car content))))
        (setq body (append body (list (car content))))
        (setq content (cdr content))))
    body))

(defun layers/add-to-layers-hash (name stages)
  "Process STAGES and add the contents to the global
`layers-hash'. NAME is the layer name."
  (while (car stages)
    (while (and (car stages)
                (not (keywordp (car stages))))
      (setq stages (cdr stages)))
    (setq wrapped-stage (append (list (car stages))
                                (layers/trim-trailing-keywords (cdr stages))))
    (layers/add-stage-to-hash name wrapped-stage)
    (setq stages (cdr stages))))

(defun layers/ensure-stages-format (stages)
  "Ensure that STAGES have the correct format. Otherwise, trigger
an error."
  (unless (keywordp (car stages))
    (layers-error (format (concat "the first element must be a keyword. "
                                  "%s is not a keyword.") (car stages)))))

;;;###autoload
(defmacro layer-def (name &rest stages)
  ""
  (declare (indent 1))
  (if (-contains? layers--layer-names name)
      (progn
        (layers/ensure-stages-format stages)
        (layers/add-to-layers-hash name stages)
        (layers/process-keywords-from-hash name))))

(provide 'layers)
;;; layers.el ends here
