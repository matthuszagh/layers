;;; layers.el --- Main file -*-lexical-binding: t;-*-
;;
;; terminology:
;;
;; + Each call to the `layer-def' macro is an instance.
;; + The layer name is the identifier that immediately follows
;;   `layer-def'.
;; + Each instance contains one or more stages. A stage is indicated by
;;   a keyword. The only required keyword is `:setup'. All others are
;;   optional.
;; + A stage includes the stage keyword and the body of the stage. The
;;   body consists of 1 or more s-expressions that (if evaluated) are
;;   evaluated as top-level sexps. I refer to these top-level sexps as
;;   forms. :depends and :conflicts are exceptions: they are simple lists
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
    :conflicts
    :presetup
    :setup
    :postsetup
    :func
    :customize)
  "doc"
  :type '(repeat symbol)
  :group 'layers)

(defsubst layers-error (msg)
  "Append layers-error: to the error message, so the error can be
tracked to this package."
  (error "%s" msg))

(defvar layers--layer-names '())
(defvar layers--unparsed-layers '())
(defvar layers--layer-deps '())
(defvar layers--layer-types '())

;; issue warning if emacs initialization completes without setting up
;; all layers.
(add-hook 'after-init-hook
          (lambda ()
            (if layers--unparsed-layers
                (dolist (layer layers--unparsed-layers)
                  (layers-error (format "layer %s never completed setup" layer))))))

(defvar layers-hash (ht)
  "Stores all layers and their contents. Each layer maps to a
sub-hashmap that in turn contains a key for each defined stage
that maps to the body for that stage.")

(defun declare-layers (layers)
  "Declare list of LAYERS to use."
  (if (not (listp layers))
      (layers-error "`declare-layers' takes a list.")
    (setq layers--layer-names layers)
    (setq layers--unparsed-layers layers)
    (dolist (layer-name layers)
      (ht-set! layers-hash layer-name (ht)))
    (provide '-layers-declaration-complete)))

(defun declare-global-depends (layer-deps)
  "Declare a list of LAYER-DEPS that should be used as
dependencies for all other layers. If these layers are not also
declared through `declare-layers', they are simply ignored."
  (with-eval-after-load '-layers-declaration-complete
    ;; remove any deps not used in `declare-layers'
    (setq layer-deps (-intersection layer-deps layers--layer-names))
    (dolist (layer-name layers--layer-names)
      (unless (-contains? layer-deps layer-name)
        (ht-set! (ht-get layers-hash layer-name) :depends layer-deps)))))

(defun layers/feature-name (layer-name stage &optional type layer-dep)
  "Generate a feature that can be used with `provide' or
`with-eval-after-load'. LAYER-NAME is the name of the layer and
STAGE is its stage. LAYER-DEP provides additional features for a
stage, which is useful with multiple presetup or postsetup
entries. These features track whether the layer has completed a
given stage."
  ;; make these into strings if they are symbols
  (unless (stringp layer-name)
    (setq layer-name (symbol-name layer-name)))
  (unless (stringp stage)
    (setq stage (symbol-name stage)))
  ;; remove initial ":" if used with stage
  (if (string= (substring stage 0 1) ":")
      (setq stage (substring stage 1 nil)))
  (if type
      (progn (unless (stringp type)
               (setq type (symbol-name type)))
             (if layer-dep
                 (progn
                   (unless (stringp layer-dep)
                     (setq layer-dep (symbol-name layer-dep)))
                   (if (string= (substring layer-dep 0 1) ":")
                       (setq layer-dep (substring layer-dep 1 nil)))
                   (intern (concat "layers-" layer-name "-" stage "-" type "-" layer-dep)))
               (intern (concat "layers-" layer-name "-" stage "-" type))))
    (intern (concat "layers-" layer-name "-" stage))))

(defun layers/layer-defines-stage? (layer-name stage)
  "Return t if layer LAYER-NAME provided stage STAGE. Otherwise
return nil."
  (ht-get (ht-get layers-hash layer-name) stage))

(defun featurep-and (feature-list)
  "Evaluate to `t' if all features in FEATURE-LIST have been
provided."
  (if (null feature-list)
      t
    (and (featurep (car feature-list)) (featurep-and (cdr feature-list)))))

(defun layers//eval-after-load-all (feature-list body)
  (if feature-list
      (dolist (feature feature-list)
        (with-eval-after-load feature
          (if (featurep-and feature-list)
              (progn
                ;; (setq after-load-alist (remove feature after-load-alist))
                (eval body)
                nil))))
    (progn ; evaluate body unconditionally if we provide empty feature list
      (eval body)
      nil)))

(defun layers/add-prepostsetup-form-to-types-hash (name form types-hash)
  "TYPES-HASH holds a map of each type associated with a list,
where the first element of the list is the priority (t or nil),
the second element is the body of the FORM and the 3rd element is
the layer dependency. FORM is a single entry in the pre or
postsetup. It has the format

;; (:layer layer-name &optional type priority
;;  (body...))

Where body consists of 1 or more sexps.
"
  (unless (keywordp (car form))
    (layers-error (concat "all pre and postsetup forms must "
                          "specify a layer using "
                          "the `:layer' keyword.")))
  (let ((layer (cadr form))
        (rest (cddr form))
        (type "nil-type")
        (priority nil))
    (if (consp layer) ; user supplied a list of layers
        (let ((all-layers-used? t))
          (dolist (l layer)
            (setq all-layers-used? (and (ht-get layers-hash l) all-layers-used?)))
          (if all-layers-used?
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
                         (append (ht-get types-hash type) (list `(,priority ,rest ,layer ,name)))))))
      ;; user supplied single layer
      ;; TODO refactor this code, it's basically identical to the list logic.
      ;; just wrap a single layer as a list and apply the same logic to both cases.
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
                     (append (ht-get types-hash type) (list `(,priority ,rest ,layer ,name)))))))))

(defun layers/schedule-presetup-forms (type val)
  "Schedule presetup forms. TYPE is the :presetup entry type and
val is a list whose first element is the priority and whose
second is the body of the :presetup entry. The third is the
dependency layer and the fourth is the name of the layer where
this :presetup stage occurs."
  ;; unconditionally evaluate all entries w/o conflict
  (if (string= type "nil-type")
      (dolist (elem val)
        (let ((body (cadr elem))
              (dep (caddr elem))
              (name (cadddr elem)))
          (if (consp dep) ; user supplied list of layers
              (let ((layer-dep-feature-list '())
                    (dep-list "")) ; turn dep list into hyphen-separated list of features
                (dolist (i dep)
                  (setq dep-list (concat dep-list (symbol-name i) "-"))
                  (setq layer-dep-feature-list
                        (append layer-dep-feature-list (list (layers/feature-name i :setup)))))
                (layers//eval-after-load-all
                 layer-dep-feature-list
                 `(unless (featurep ',(layers/feature-name name :setup))
                    (dolist (form ',body)
                      (eval form))
                    (provide ',(layers/feature-name name :presetup type dep-list)))))
            ;; user supplied single layer
            (with-eval-after-load (layers/feature-name dep :setup)
              ;; don't want presetup body reevaluated each time setup is evaluated
              (unless (featurep (layers/feature-name name :setup))
                (dolist (form body)
                  (eval form))
                (provide (layers/feature-name name :presetup type dep)))))))
    (let ((priority-exists? (layers/priority-existsp val)))
      (dolist (elem val)
        (let ((priority (car elem))
              (body (cadr elem))
              (dep (caddr elem))
              (name (cadddr elem)))
          ;; if at least one entry has set priority, only evaluate entries with priority.
          ;; otherwise, evaluate all entries.
          ;; TODO code needs major refactoring, most of it is identical
          (if (and priority-exists?
                   priority)
              (if (consp dep)
                  (let ((layer-dep-feature-list '())
                        (dep-list ""))
                    (dolist (i dep)
                      (setq dep-list (concat dep-list (symbol-name i) "-"))
                      (setq layer-dep-feature-list
                            (append layer-dep-feature-list (list (layers/feature-name i :setup)))))
                    (layers//eval-after-load-all
                     layer-dep-feature-list
                     `(unless (featurep ',(layers/feature-name name :setup))
                        (dolist (form ',body)
                          (eval form))
                        (provide ',(layers/feature-name name :presetup type dep-list)))))
                (with-eval-after-load (layers/feature-name dep :setup)
                  (unless (featurep (layers/feature-name name :setup))
                    (dolist (form body)
                      (eval form))
                    (provide (layers/feature-name name :presetup type dep)))))
            (if (consp dep)
                (let ((layer-dep-feature-list '())
                      (dep-list ""))
                  (dolist (i dep)
                    (setq dep-list (concat dep-list (symbol-name i) "-"))
                    (setq layer-dep-feature-list
                          (append layer-dep-feature-list (list (layers/feature-name i :setup)))))
                  (layers//eval-after-load-all
                   layer-dep-feature-list
                   `(unless (featurep ',(layers/feature-name name :setup))
                      (dolist (form ',body)
                        (eval form))
                      (provide ',(layers/feature-name name :presetup type dep-list)))))
              (with-eval-after-load (layers/feature-name dep :setup)
                (unless (featurep (layers/feature-name name :setup))
                  (dolist (form body)
                    (eval form))
                  (provide (layers/feature-name name :presetup type dep)))))))))))

(defun layers-handler/:presetup (hash body name)
  "Handles processing of the :presetup body. HASH is the hash map
for the current layer and BODY is :presetup's wrapped
body. Handle processing by first constructing a `types-hash'
where the key is the type of each form ('nil-type' for forms
without a type) and value is a list whose first element is the
priority (t or nil) and whose second element is wrapped body of
the form."
  ;; only evaluate presetup once, before the setup has been evaluated
  (unless (featurep (layers/feature-name name :setup))
    (let ((types-hash (ht ("nil-type" '()))))
      (dolist (form body)
        (layers/add-prepostsetup-form-to-types-hash name form types-hash))
      (ht-map 'layers/schedule-presetup-forms types-hash)
      (setq presetup-types (ht-keys types-hash))
      (setq presetup-type-features '()) ; prerequisite features to provide presetup
      (dolist (type presetup-types)
        (setq deps '())
        (setq presetup-type-deps-features '()) ; prerequisite features to provide presetup type features
        (dolist (dep (mapcar 'caddr (ht-get types-hash type)))
          ;; TODO why is this here? i don't use it
          ;; (setq deps (append deps (list dep)))
          (if (consp dep)
              (let ((dep-list ""))
                (dolist (i dep)
                  (setq dep-list (concat dep-list (symbol-name i) "-")))
                (setq dep dep-list)))
          (setq presetup-type-deps-features
                (append presetup-type-deps-features
                        (list (layers/feature-name name :presetup type dep)))))
        (layers//eval-after-load-all presetup-type-deps-features
                                     `(provide ',(layers/feature-name name :presetup type)))
        (setq presetup-type-features
              (append presetup-type-features (list (layers/feature-name name :presetup type)))))
      (layers//eval-after-load-all presetup-type-features
                                   `(provide ',(layers/feature-name name :presetup))))))

(defun layers-handler/:setup (hash body name)
  "Schedule evaluation for :setup stage's BODY. HASH is the stage
hash map and NAME is the layer name. Evaluate all applicable
forms now, or specify their future evaluation dependencies unmet."
  (unless body
    (layers-error (format (concat "mandatory :setup stage ommitted "
                                  "for layer %s") name)))
  (let ((deps (ht-get hash :depends))
        (prereq-features (list (layers/feature-name name "presetup"))))
    (if deps
        (setq prereq-features
              (append prereq-features (mapcar (lambda (dep)
                                                (layers/feature-name dep "setup")) deps))))
    (if (featurep (layers/feature-name name "setup"))
        (dolist (form body)
          (eval form))
      (layers//eval-after-load-all prereq-features
                                   `(progn ,@body
                                           (provide ',(layers/feature-name name "setup")))))))

(defun layers/priority-existsp (type-hash-val)
  "Return t if any entries in a pre or postsetup for a given type
have a priority set. TYPE-HASH-VAL is the value of the
type-hash."
  (dolist (entry type-hash-val)
    (if (car entry)
        t)))

(defun layers/schedule-postsetup-forms (type val)
  "Schedule postsetup forms. TYPE is the :postsetup entry type and
val is a list whose first element is the priority and whose
second is the body of the :postsetup entry.
TODO there are more than 2 elements. Document them!"
  (dolist (elem val)
    (let ((priority (car elem))
          (body (nth 1 elem))
          (dep (nth 2 elem))
          (name (nth 3 elem)))
      (if (featurep (layers/feature-name name :postsetup))
          (dolist (form body)
            (eval form))
        (if (string= type "nil-type")
            (if dep
                (if (consp dep)
                    (let ((dep-feature-list '()))
                      (dolist (i dep)
                        (setq dep-feature-list
                              (append dep-feature-list
                                      (list (layers/feature-name i :setup)))))
                      (setq dep-feature-list
                            (append dep-feature-list
                                    (list (layers/feature-name name :setup))))
                      (layers//eval-after-load-all
                       dep-feature-list
                       `(progn
                          (dolist (form ',body)
                            (eval form)
                            (provide ',(layers/feature-name name :postsetup))))))
                  (layers//eval-after-load-all
                   (append
                    (list (layers/feature-name name :setup))
                    (list (layers/feature-name dep :setup)))
                   `(progn
                      (dolist (form ',body)
                        (eval form)
                        (provide ',(layers/feature-name name :postsetup))))))
              (with-eval-after-load (layers/feature-name name :setup)
                (dolist (form body)
                  (eval form))
                (provide (layers/feature-name name :postsetup))))
          (let ((priority-exists? (layers/priority-existsp val)))
            (if (and priority-exists?
                     priority)
                (if dep
                    (if (consp dep)
                        (let ((dep-feature-list '()))
                          (dolist (i dep)
                            (setq dep-feature-list
                                  (append dep-feature-list
                                          (list (layers/feature-name i :setup)))))
                          (setq dep-feature-list
                                (append dep-feature-list
                                        (list (layers/feature-name name :setup))))
                          (layers//eval-after-load-all
                           dep-feature-list
                           `(progn
                              (dolist (form ',body)
                                (eval form)
                                (provide ',(layers/feature-name name :postsetup))))))
                      (layers//eval-after-load-all
                       (append
                        (list (layers/feature-name name :setup))
                        (list (layers/feature-name dep :setup)))
                       `(progn
                          (dolist (form ',body)
                            (eval form)
                            (provide ',(layers/feature-name name :postsetup))))))
                  (with-eval-after-load (layers/feature-name name :setup)
                    (dolist (form body)
                      (eval form))
                    (provide (layers/feature-name name :postsetup))))
              (if dep
                  (if (consp dep)
                      (let ((dep-feature-list '()))
                        (dolist (i dep)
                          (setq dep-feature-list
                                (append dep-feature-list
                                        (list (layers/feature-name i :setup)))))
                        (setq dep-feature-list
                              (append dep-feature-list
                                      (list (layers/feature-name name :setup))))
                        (layers//eval-after-load-all
                         dep-feature-list
                         `(dolist (form ',body)
                            (provide ',(layers/feature-name name :postsetup)))))
                    (layers//eval-after-load-all
                     (append
                      (list (layers/feature-name name :setup))
                      (list (layers/feature-name dep :setup)))
                     `(progn
                        (dolist (form ',body)
                          (eval form)
                          (provide ',(layers/feature-name name :postsetup))))))
                (with-eval-after-load (layers/feature-name name :setup)
                  (dolist (form body)
                    (eval form))
                  (provide (layers/feature-name name :postsetup)))))))))))

(defun layers-handler/:postsetup (hash body name)
  "Handles processing of the :postsetup body. HASH is the hash
map for the current layer and BODY is :postsetup's wrapped
body. Handle processing by first constructing a `types-hash'
where the key is the type of each form ('nil-type' for forms
without a type) and value is a list whose first element is the
priority (t or nil) and whose second element is the wrapped body
of the form."
  (let ((types-hash (ht ("nil-type" '()))))
    (dolist (form body)
      (layers/add-prepostsetup-form-to-types-hash name form types-hash))
    (ht-map 'layers/schedule-postsetup-forms types-hash)))

(defun layers-handler/:func (_hash body name)
  ""
  (if (featurep (layers/feature-name name :func))
      (dolist (form body)
        (eval form))
    (with-eval-after-load (layers/feature-name name :postsetup)
      (dolist (form body)
        (eval form))
      (provide (layers/feature-name name :func))))
  nil)

(defun layers-handler/:customize (_hash body name)
  ""
  (if (featurep (layers/feature-name name :customize))
      (dolist (form body)
        (eval form))
    (with-eval-after-load (layers/feature-name name :func)
      (dolist (form body)
        (eval form))
      (provide (layers/feature-name name :customize))))
  nil)

(defun layers/add-stage-to-hash (name stage)
  "Take a single, wrapped stage and add it to the global
`layers-hash'. NAME is the layer name and STAGE is the stage to
add."
  (let ((stage-name (car stage))
        (stage-body (cdr stage)))
    (if (eq stage-name :depends)
        (ht-set! (ht-get layers-hash name) stage-name (car stage-body))
      (ht-set! (ht-get layers-hash name) stage-name stage-body))))

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
    (provide '-layers-setup-complete))
  (let ((layer-hash (ht-get layers-hash name)))
    ;; :setup will only proceed after :presetup is complete
    (if (and (not (layers/layer-defines-stage? name :presetup))
             ;; providing presetup again if setup is already provided causes setup to be
             ;; evaluated multiple times.
             (not (featurep (layers/feature-name name :setup))))
        (provide (layers/feature-name name :presetup)))
    (layers//handle-keyword layer-hash :presetup (symbol-name name))

    (layers//handle-keyword layer-hash :setup (symbol-name name))

    ;; if user doesn't supply postsetup and it hasn't been provided,
    ;; then provide a dummy postsetup. otherwise, handle it normally
    (if (and (not (layers/layer-defines-stage? name :postsetup))
             (not (featurep (layers/feature-name name :postsetup))))
        (provide (layers/feature-name name :postsetup)))
    (layers//handle-keyword layer-hash :postsetup (symbol-name name))

    (if (and (not (layers/layer-defines-stage? name :func))
             (not (featurep (layers/feature-name name :func))))
        (provide (layers/feature-name name :func)))
    (layers//handle-keyword layer-hash :func (symbol-name name))

    (if (and (not (layers/layer-defines-stage? name :customize))
             (not (featurep (layers/feature-name name :customize))))
        (provide (layers/feature-name name :customize)))
    (layers//handle-keyword layer-hash :customize (symbol-name name))))

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
