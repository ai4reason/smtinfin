(setq *cvc5* "cvc5")
(setq *tlimitms* 500)

(setq *verbosity* 0)
(setq *convert* nil)
(setq *lash* nil)

(setq *beamsize* 60)
(setq *synthdepth* 7)
(setq *keepfac* 6)

(setq *bc* 0)
(setq *bcl* nil)
(setq *cc* 0)
(setq *ccl* nil)
(setq *unittp* nil)
(setq *interptp* nil)
(setq *interpfunc* nil)
(setq *interpconst* nil)
(setq *ret-unit* (make-hash-table :test #'equal))
(setq *arg-unit* (make-hash-table :test #'equal))

(defun rename-special-symbols (m)
  (if (consp m)
      (cons (rename-special-symbols (car m)) (rename-special-symbols (cdr m)))
    (if (eq m t)
	'|t|
      m)))

(setq *break-before-cvc5* nil)

(defun call-lash (fn)
  (let ((p (run-program *lash* (list "-M" "/dev" "-m" "null" "-t" "0.5" fn) :output :stream))
	(sl nil)
	(l nil))
    (catch 'result
      (loop while (setq l (read-line (process-output p) nil nil)) do
	    (when (> *verbosity* 76) (format t "lashout:~d~%" l))
	    (when (equal l "% SZS status Unsatisfiable")
	      (progn (close (process-output p)) (throw 'result 'UNSAT))))
      (close (process-output p))
      nil)))
  
(defun call-cvc5 (fn)
  (when *break-before-cvc5* (break))
  (let ((p (run-program *cvc5* (list (format nil "--tlimit=~d" *tlimitms*) fn) :output :stream))
	(l nil))
    (let ((r
	   (catch 'result
	     (loop while (setq l (read-line (process-output p) nil nil)) do
		   (cond ((equal l "sat") (close (process-output p)) (throw 'result 'sat))
			 ((equal l "unsat") (close (process-output p)) (throw 'result 'unsat))
			 ((equal l "unknown") (close (process-output p)) (throw 'result 'unknown))
			 (t nil)))
	     (close (process-output p))
	     nil)))
      (if (member r '(SAT UNSAT))
	  r
	(let ((p (run-program *cvc5* (list "--cegqi-all" (format nil "--tlimit=~d" *tlimitms*) fn) :output :stream))
	      (l nil))
	  (let ((r
		 (catch 'result
		   (loop while (setq l (read-line (process-output p) nil nil)) do
			 (cond ((equal l "sat") (close (process-output p)) (throw 'result 'sat))
			       ((equal l "unsat") (close (process-output p)) (throw 'result 'unsat))
			       ((equal l "unknown") (close (process-output p)) (throw 'result 'unknown))
			       (t nil)))
		   (close (process-output p))
		   nil)))
	    (if (member r '(SAT UNSAT))
		r
	      (let ((p (run-program *cvc5* (list "--enum-inst" (format nil "--tlimit=~d" *tlimitms*) fn) :output :stream))
		    (l nil))
		(catch 'result
		  (loop while (setq l (read-line (process-output p) nil nil)) do
			(cond ((equal l "sat") (close (process-output p)) (throw 'result 'sat))
			      ((equal l "unsat") (close (process-output p)) (throw 'result 'unsat))
			      ((equal l "unknown") (close (process-output p)) (throw 'result 'unknown))
			      (t nil)))
		  (close (process-output p))
		  nil)))))))))

(defun interptp (a)
  (cond ((eq a 'INT) "Int")
	((eq a 'BOOL) "Bool")
	(t
	 (let ((b (assoc a *interptp* :test #'equal)))
	   (if b
	       (case (cdr b)
		     (INT "Int")
		     (BOOL "Bool")
		     (t (cdr b)))
	     (format nil "~d" a))))))

(defun interptrm (m &optional unitvars)
  (if (consp m)
      (case (car m)
	    (! (interptrm (cadr m) unitvars))
	    (FORALL
	     (interptrm-forall (cadr m) (caddr m) unitvars))
	    (EXISTS
	     (interptrm-exists (cadr m) (caddr m) unitvars))
	    (LET
	     (interptrm-let (cadr m) (caddr m) unitvars))
	    (not
	     (format nil "(not ~d)" (interptrm (cadr m) unitvars)))
	    (and
	     (format nil "(and~d)" (interptrm-junc (cdr m) unitvars)))
	    (or
	     (format nil "(or~d)" (interptrm-junc (cdr m) unitvars)))
	    (true
	     (format nil "true"))
	    (false
	     (format nil "false"))
	    (=
	     (if (or (unit-trm-p (cadr m) unitvars)
		     (unit-trm-p (caddr m) unitvars))
		 "true"
	       (format nil "(= ~d ~d)" (interptrm (cadr m) unitvars) (interptrm (caddr m) unitvars))))
	    (distinct
	     (let ((r (format nil "(distinct")))
	       (dolist (n (cdr m) (format nil "~d)" r))
		 (setq r (format nil "~d ~d" r (interptrm n unitvars))))))
	    (=>
	     (format nil "(=> ~d ~d)" (interptrm (cadr m) unitvars) (interptrm (caddr m) unitvars)))
	    (<=
	     (format nil "(<= ~d ~d)" (interptrm (cadr m) unitvars) (interptrm (caddr m) unitvars)))
	    (<
	     (format nil "(< ~d ~d)" (interptrm (cadr m) unitvars) (interptrm (caddr m) unitvars)))
	    (+
	     (format nil "(+ ~d ~d)" (interptrm (cadr m) unitvars) (interptrm (caddr m) unitvars)))
	    (-
	     (if (cddr m)
		 (format nil "(- ~d ~d)" (interptrm (cadr m) unitvars) (interptrm (caddr m) unitvars))
	       (format nil "(- ~d)" (interptrm (cadr m) unitvars))))
	    (HALVE (format nil "(div ~d 2)" (interptrm (cadr m) unitvars)))
	    (DOUBLE (format nil "(* 2 ~d)" (interptrm (cadr m) unitvars)))
	    (ITE
	     (format nil "(ite ~d ~d ~d)"
		     (interptrm (cadr m) unitvars)
		     (interptrm (caddr m) unitvars)
		     (interptrm (cadddr m) unitvars)))
	    (NNEG
	     (format nil "(<= 0 ~d)" (interptrm (cadr m) unitvars)))
	    (EVENP
	     (format nil "(exists ((N Int)) (= (* 2 N) ~d))" (interptrm (cadr m) unitvars)))
	    (SYGUSF
	     (format nil "(SYGUSF ~d)" (interptrm (cadr m) unitvars)))
	    (t
	     (let ((f (assoc (car m) *interpfunc* :test #'equal)))
	       (if f
		   (interptrm (apply (cdr f) (cdr m)) unitvars)
		 (let* ((s (mapcar #'(lambda (n) (interptrm n unitvars)) (cdr m)))
			(s2 (drop-unit-args (car m) 1 s)))
		   (if (equal s2 "")
		       (format nil "~d" (car m))
		     (format nil "(~d~d)" (car m) s2)))))))
    (let ((c (assoc m *interpconst* :test #'equal)))
      (if c
	  (cdr c)
	(case m
	      (FALSE "false")
	      (TRUE "true")
	      (t
	       (format nil "~d" m)))))))

(defun drop-unit-args (fn i s)
  (if s
      (if (gethash (cons fn i) *arg-unit*)
	  (drop-unit-args fn (1+ i) (cdr s))
	(format nil " ~d~d" (car s) (drop-unit-args fn (1+ i) (cdr s))))
    ""))

(defun interptrm-spine (ml &optional unitvars)
  (if ml
      (format nil " ~d~d" (interptrm (car ml) unitvars) (interptrm-spine (cdr ml) unitvars))
    ""))

(defun interptrm-junc (ml unitvars)
  (if ml
      (format nil " ~d~d" (interptrm (car ml) unitvars) (interptrm-junc (cdr ml) unitvars))
    ""))

(defun interptrm-let (vl body &optional unitvars ll)
  (if vl
      (let ((x (caar vl))
	    (m (cadar vl)))
	(if (unit-trm-p m unitvars)
	    (interptrm-let (cdr vl) body (cons x unitvars) ll)
	  (let ((ms (interptrm m unitvars)))
	    (interptrm-let (cdr vl) body unitvars (if ll (format nil "~d (~d ~d)" ll x ms) (format nil "(~d ~d)" x ms))))))
    (if ll
	(format nil "(let (~d) ~d)" ll (interptrm body unitvars))
      (interptrm body unitvars))))

(defun interptrm-forall (vl body &optional unitvars)
  (if vl
      (if (member (cadar vl) *unittp* :test #'equal)
	  (interptrm-forall (cdr vl) body (cons (caar vl) unitvars))
	(format nil "(forall ((~d ~d)) ~d)" (caar vl) (interptp (cadar vl))
		(interptrm-forall (cdr vl) body unitvars)))
    (interptrm body unitvars)))

(defun interptrm-exists (vl body &optional unitvars)
  (if vl
      (if (member (cadar vl) *unittp* :test #'equal)
	  (interptrm-exists (cdr vl) body (cons (caar vl) unitvars))
	(format nil "(exists ((~d ~d)) ~d)" (caar vl) (interptp (cadar vl))
		(interptrm-exists (cdr vl) body unitvars)))
    (interptrm body unitvars)))

(defun th0ify (m vars)
  (let ((n (format nil "~d" m)))
    (if (and (> (length n) 0) (eq (aref n 0) #\?))
	(format nil "X~d" (subseq n 1))
      (if (member m vars)
	  (format nil "X~d" n)
	(format nil "c~d" n)))))
  
(defun interptp-th0 (a)
  (cond ((eq a 'INT) "$i")
	((eq a 'BOOL) "$o")
	(t
	 (let ((b (assoc a *interptp* :test #'equal)))
	   (if b
	       (case (cdr b)
		     (INT "$i")
		     (BOOL "$o")
		     (t (cdr b)))
	     (format nil "c~d" a))))))

(defun interptrm-th0 (m &optional unitvars vars)
  (if (consp m)
      (case (car m)
	    (! (interptrm-th0 (cadr m) unitvars vars))
	    (FORALL
	     (interptrm-th0-forall (cadr m) (caddr m) unitvars vars))
	    (EXISTS
	     (interptrm-th0-exists (cadr m) (caddr m) unitvars vars))
	    (LET (throw 'th0-fail nil))
	    (not
	     (format nil "(~~(~d))" (interptrm-th0 (cadr m) unitvars vars)))
	    (and
	     (if (cdr m)
	         (format nil "(~d)" (interptrm-th0-junc "&" (cdr m) unitvars vars))
	       "$true"))
	    (or
	     (if (cdr m)
		 (format nil "(~d)" (interptrm-th0-junc "|" (cdr m) unitvars vars))
	       "$false"))
	    (true
	     (format nil "$true"))
	    (false
	     (format nil "$false"))
	    (=
	     (if (or (unit-trm-p (cadr m) unitvars)
		     (unit-trm-p (caddr m) unitvars))
		 "$true"
	       (format nil "(~d = ~d)" (interptrm-th0 (cadr m) unitvars vars) (interptrm-th0 (caddr m) unitvars vars))))
	    (distinct (throw 'th0-fail nil))
	    (=>
	     (format nil "(~d => ~d)" (interptrm-th0 (cadr m) unitvars vars) (interptrm-th0 (caddr m) unitvars vars)))
	    (<= (throw 'th0-fail nil))
	    (< (throw 'th0-fail nil))
	    (+ (throw 'th0-fail nil))
	    (- (throw 'th0-fail nil))
	    (HALVE (throw 'th0-fail nil))
	    (DOUBLE (throw 'th0-fail nil))
	    (ITE (throw 'th0-fail nil))
	    (NNEG (throw 'th0-fail nil))
	    (EVENP (throw 'th0-fail nil))
	    (SYGUSF (throw 'th0-fail nil))
	    (t
	     (let ((f (assoc (car m) *interpfunc* :test #'equal)))
	       (if f
		   (interptrm-th0 (apply (cdr f) (cdr m)) unitvars vars)
		 (let* ((s (mapcar #'(lambda (n) (interptrm-th0 n unitvars vars)) (cdr m)))
			(s2 (drop-unit-args-th0 (car m) 1 s)))
		   (if (equal s2 "")
		       (format nil "c~d" (car m))
		     (format nil "(c~d~d)" (car m) s2)))))))
    (let ((c (assoc m *interpconst* :test #'equal)))
      (if c
	  (cdr c)
	(case m
	      (FALSE "$false")
	      (TRUE "$true")
	      (t
	       (th0ify m vars)))))))

(defun interptrm-th0-spine (ml &optional unitvars vars)
  (if ml
      (format nil " @ ~d~d" (interptrm-th0 (car ml) unitvars vars) (interptrm-th0-spine (cdr ml) unitvars vars))
    ""))

(defun interptrm-th0-junc (j ml unitvars vars)
  (if ml
      (if (cdr ml)
          (format nil "~d ~d ~d" (interptrm-th0 (car ml) unitvars vars) j (interptrm-th0-junc j (cdr ml) unitvars vars))
        (format nil "~d" (interptrm-th0 (car ml) unitvars vars)))
    ""))

(defun interptrm-th0-forall (vl body &optional unitvars vars)
  (if vl
      (if (member (cadar vl) *unittp* :test #'equal)
	  (interptrm-th0-forall (cdr vl) body (cons (caar vl) unitvars))
	(format nil "(! [~d:~d] : ~d)" (th0ify (caar vl) (cons (caar vl) vars)) (interptp-th0 (cadar vl))
		(interptrm-th0-forall (cdr vl) body unitvars (cons (caar vl) vars))))
    (interptrm-th0 body unitvars vars)))

(defun interptrm-th0-exists (vl body &optional unitvars vars)
  (if vl
      (if (member (cadar vl) *unittp* :test #'equal)
	  (interptrm-th0-exists (cdr vl) body (cons (caar vl) unitvars))
	(format nil "(? [~d:~d] : ~d)" (th0ify (caar vl) (cons (caar vl) vars)) (interptp-th0 (cadar vl))
		(interptrm-th0-exists (cdr vl) body unitvars (cons (caar vl) vars))))
    (interptrm-th0 body unitvars vars)))

(defun drop-unit-args-th0 (fn i s)
  (if s
      (if (gethash (cons fn i) *arg-unit*)
	  (drop-unit-args fn (1+ i) (cdr s))
	(format nil " @ ~d~d" (car s) (drop-unit-args-th0 fn (1+ i) (cdr s))))
    ""))

(defun unit-trm-p (m unitvars)
  (if (consp m)
      (gethash (car m) *ret-unit*)
    (or (gethash m *ret-unit*) (member m unitvars :test #'equal))))

(defun trivial-after-interp (m &optional unitvars)
  (cond ((and (consp m) (eq (car m) '=))
	 (or (unit-trm-p (cadr m) unitvars)
	     (unit-trm-p (caddr m) unitvars)))
	((and (consp m) (eq (car m) '=>))
	 (trivial-after-interp (caddr m) unitvars))
	((and (consp m) (eq (car m) 'forall))
	 (trivial-after-interp-forall (cadr m) (caddr m) unitvars))
	(t nil)))

(defun trivial-after-interp-forall (vl body unitvars)
  (if vl
      (if (member (cadar vl) *unittp* :test #'equal)
	  (trivial-after-interp-forall (cdr vl) body (cons (caar vl) unitvars))
	(trivial-after-interp-forall (cdr vl) body unitvars))
    (trivial-after-interp body unitvars)))

(defun readsmt (fn)
  (setq *ret-unit* (make-hash-table :test #'equal))
  (setq *arg-unit* (make-hash-table :test #'equal))
  (let ((f (open fn :direction :input))
	(sortl nil)
	(funl nil)
	(al nil)
	(ll nil))
    (loop while (setq x (read f nil nil)) do
	  (when (consp x)
	    (case (car x)
		  (declare-sort
		   (unless (equal (caddr x) 0) (throw 'fail '(fail "cannot handle sorts with arguments")))
		   (push (rename-special-symbols (cadr x)) sortl))
		  (declare-const
		   (push (list (rename-special-symbols (cadr x)) nil (rename-special-symbols (caddr x))) funl))
		  (declare-fun
		   (push (rename-special-symbols (cdr x)) funl))
		  (assert
		   (push (rename-special-symbols (cadr x)) al))
		  (t (push x ll)))))
    (close f)
    (values (reverse ll) (reverse sortl) (reverse funl) (reverse al))))
  
(defun interpsmt (ll gn)
  (setq *ret-unit* (make-hash-table :test #'equal))
  (setq *arg-unit* (make-hash-table :test #'equal))
  (let ((i 0)
	(g (open gn :direction :output :if-exists :supersede)))
    (dolist (x ll)
      (case (car x)
	    (declare-sort
	     (unless (or (assoc (cadr x) *interptp* :test #'equal) (member (cadr x) *unittp* :test #'equal))
	       (format g "(declare-sort ~d 0)~%" (cadr x))))
	    (declare-fun
	     (if (member (cadddr x) *unittp* :test #'equal)
		 (setf (gethash (cadr x) *ret-unit*) t)
	       (unless (or (assoc (cadr x) *interpfunc* :test #'equal) (assoc (cadr x) *interpconst* :test #'equal))
			 
		 (format g "(declare-fun ~d (" (cadr x))
		 (setq i 0)
		 (dolist (y (caddr x))
		   (incf i)
		   (if (member y *unittp* :test #'equal)
		       (setf (gethash (cons (cadr x) i) *arg-unit*) t)
		     (format g " ~d" (interptp y))))
		 (format g ") ~d)~%" (interptp (cadddr x))))))
	    (assert
	     (unless (trivial-after-interp (cadr x))
	       (format g "(assert ~d)~%" (interptrm (cadr x)))))
	    (check-sat (format g "(check-sat)~%"))
	    (set-info
	     (format g "(set-info")
	     (dolist (y (cdr x)) (format g " ~S" y))
	     (format g ")~%"))
	    (set-logic
	     (format g "(set-logic")
	     (dolist (y (cdr l))
	       (if (eq y 'UF)
		   (format g " UFLIA") ; extend to UFLIA to have Int
		 (format g " ~S" y)))
	     (format g ")~%"))
	    (exit (format g "(exit)~%"))
	    (t
	     (format g "~S~%" x))))
    (close g)))

(setq *infsort* (make-hash-table :test #'equal))
(setq *nonunitsort* (make-hash-table :test #'equal))
(setq *retsort* (make-hash-table :test #'equal))
(setq *argsorts* (make-hash-table :test #'equal))

(defun has-sort (cx m)
  (if (consp m)
      (gethash (car m) *retsort*)
    (or (gethash m *retsort*)
	(let ((a (assoc m cx)))
	  (when a (cadr a))))))

(defun check-assert-nonunit (m &optional cx (p t))
  (if (consp m)
      (case (car m)
	    (not (check-assert-nonunit (cadr m) cx (not p)))
	    (! (check-assert-nonunit (cadr m) cx p))
	    ((forall exists) (check-assert-nonunit-quant (cadr m) (caddr m) cx p))
	    (and
	     (when p
	       (dolist (n (cdr m)) (check-assert-nonunit n cx p))))
	    (or
	     (unless p
	       (dolist (n (cdr m)) (check-assert-nonunit n cx p))))
	    (=>
	     (unless p
	       (check-assert-nonunit (cadr m) cx (not p))
	       (check-assert-nonunit (caddr m) cx p)))
	    (distinct
	     (when (and p (cddr m))
	       (let ((n (find-if #'(lambda (n) (has-sort cx n)) (cdr m))))
		 (when n
		   (let ((a (has-sort cx n)))
		     (setf (gethash a *nonunitsort*) t))))))
	    (=
	     (unless p
	       (let ((a (has-sort cx (cadr m))))
		 (unless a (setq a (has-sort cx (caddr m))))
		 (when a
		   (setf (gethash a *nonunitsort*) t)))))
	    (t nil))
    nil))

(defun check-assert-nonunit-quant (bvl body cx p)
  (check-assert-nonunit body (append (reverse bvl) cx) p))

(defun distinct-bvars-p (ml cx &optional used)
  (if ml
      (if (and (member (car ml) cx :test #'equal) (not (member (car ml) used :test #'equal)))
	  (distinct-bvars-p (cdr ml) cx (cons (car ml) used))
	nil)
    t))

(defun fun-used-in-p (f m)
  (if (consp m)
      (if (equal (car m) f)
	  t
	(if (eq (car m) '(forall exists))
	    (fun-used-in-p f (caddr m))
	  (find-if #'(lambda (n) (fun-used-in-p f n)) (cdr m))))
    nil))

(defun uninterp-fun-used-in-p (m)
  (if (consp m)
      (if (member (car m) '(forall exists))
	  (uninterp-fun-used-in-p (caddr m))
	(if (member (car m) '(<=> => and or in not ! < <= = * + div - ite))
	    (find-if #'(lambda (n) (uninterp-fun-used-in-p n)) (cdr m))
	  t))
    nil))

(defun free-in (x m)
  (if (consp m)
      (case (car m)
	    ((forall exists)
	     (if (assoc x (cadr m))
		 nil
	       (free-in x (caddr m))))
	    (t
	     (find-if #'(lambda (n) (free-in x n)) m)))
    (eq x m)))

(defun synthterms ()
  (let ((tl nil)
	(kp nil))
    (dotimes (i *synthdepth* kp)
      (let* ((l (synthterm i *beamsize*))
	     (l2 (if (> (length l) (* (1+ i) *keepfac*)) (subseq l 0 (* (1+ i) *keepfac*)) l)))
	(setq kp (union kp (mapcar #'car l2) :test #'equal))))))

(defun synthprops ()
  (let ((tl nil)
	(kp nil))
    (dotimes (i *synthdepth* kp)
      (let* ((l (synthprop i *beamsize*))
	     (l2 (if (> (length l) (* (1+ i) *keepfac*)) (subseq l 0 (* (1+ i) *keepfac*)) l)))
	(setq kp (union kp (mapcar #'car l2) :test #'equal))))))

(defun check-eq-infinite (v f args cx hyps)
  (let ((va (assoc v cx)))
    (when (and va
	       (eq (cadr va) 'Int))
      (let ((vhyps (remove-if-not #'(lambda (h) (free-in v h)) hyps)))
	(when (or (not vhyps)
		  (and (not (cdr vhyps))
		       (consp (car vhyps))
		       (member (caar vhyps) '(<= <))
		       (or (and (eq (cadar vhyps) v)
				(not (free-in v (caddar vhyps))))
			   (and (eq (caddar vhyps) v)
				(not (free-in v (cadar vhyps)))))))
	  (let ((vused nil))
	    (dotimes (i (length args))
	      (let ((m (nth i args)))
		(when (free-in v m)
		  (push (cons i m) vused))))
	    (when (equal (length vused) 1)
	      (let* ((i (caar vused))
		     (m (cdar vused))
		     (a (nth i (gethash f *argsorts*))))
		(unless (member a '(INT BOOL))
		  (when (consp m)
		    (setf (gethash a *infsort*) t)))))))))))

(defun check-assert-infinite (m &optional cx hyps (p t))
  (if (consp m)
      (case (car m)
	    (not (check-assert-infinite (cadr m) cx hyps (not p)))
	    (! (check-assert-infinite (cadr m) cx hyps p))
	    (forall
	     (when p
	       (check-assert-infinite (caddr m) (append (reverse (cadr m)) cx) hyps p)))
	    (exists
	     (unless p
	       (check-assert-infinite (caddr m) (append (reverse (cadr m)) cx) hyps p)))
	    (=>
	     (when p
	       (check-assert-infinite (caddr m) cx (cons (cadr m) hyps) p)))
	    (=
	     (when p
	       (if (consp (cadr m))
		   (unless (consp (caddr m))
		     (check-eq-infinite (caddr m) (caadr m) (cdadr m) cx hyps))
		 (when (consp (caddr m))
		   (check-eq-infinite (cadr m) (caaddr m) (cdaddr m) cx hyps)))))
	    (t nil))
    nil))

(defun interpreted-sort (a sortposs)
  (let ((x (assoc a sortposs :test #'equal)))
    (if x
	(cdr x)
      a)))

(defun split-consts-and-quote (m)
  (if (eq m 'C)
      (let ((c (read-from-string (format nil "C~d" *cc*))))
	(incf *cc*)
	(push c *ccl*)
	(list 'quote c))
    (if (eq m 'B)
	(let ((c (read-from-string (format nil "B~d" *bc*))))
	  (incf *bc*)
	  (push c *bcl*)
	  (list 'quote c))
      (if (consp m)
	  (if (eq (car m) 'VAR)
	      (cadr m)
	    (cons 'list (cons (list 'quote (car m)) (mapcar #'(lambda (n) (split-consts-and-quote n)) (cdr m)))))
	(if (eq m 'X)
	    'X
	  (list 'quote m))))))

(defun split-consts-and-dquote (m)
  (if (eq m 'C)
      (let ((c (read-from-string (format nil "C~d" *cc*))))
	(incf *cc*)
	(push c *ccl*)
	(list 'quote c))
    (if (eq m 'B)
	(let ((c (read-from-string (format nil "B~d" *bc*))))
	  (incf *bc*)
	  (push c *bcl*)
	  (list 'quote c))
      (if (consp m)
	  (if (eq (car m) 'VAR)
	      (cadr m)
	    (cons 'list (cons (list 'quote (car m)) (mapcar #'(lambda (n) (split-consts-and-quote n)) (cdr m)))))
	(if (eq m 'X)
	    'X
	  (list 'quote m))))))

(defun output-interp-smt-real (g ll sortl funl al)
  (dolist (l ll)
    (case (car l)
	  (set-info
	   (format g "(set-info")
	   (dolist (y (cdr l)) (format g " ~S" y))
	   (format g ")~%"))
	  (set-logic
	   (format g "(set-logic")
	   (dolist (y (cdr l))
	     (if (eq y 'UF)
		 (format g " UFLIA") ; extend to UFLIA to have Int
	       (format g " ~S" y)))
	   (format g ")~%"))
	  (t nil)))
  (dolist (x sortl)
    (unless (or (assoc x *interptp* :test #'equal) (member x *unittp* :test #'equal))
      (format g "(declare-sort ~d 0)~%" x)))
  (dolist (x funl)
    (unless (gethash (car x) *ret-unit*)
      (unless (or (assoc (car x) *interpfunc* :test #'equal)
		  (assoc (car x) *interpconst* :test #'equal))
	(format g "(declare-fun ~d (" (car x))
	(setq i 0)
	(dolist (y (cadr x))
	  (incf i)
	  (if (member y *unittp* :test #'equal)
	      (setf (gethash (cons (car x) i) *arg-unit*) t)
	    (format g " ~d" (interptp y))))
	(format g ") ~d)~%" (interptp (caddr x))))))
  (dolist (c *bcl*)
    (format g "(declare-fun ~d () Bool)~%" c))
  (dolist (c *ccl*)
    (format g "(declare-fun ~d () Int)~%" c))
  (dolist (m al)
    (unless (trivial-after-interp m)
      (format g "(assert ~d)~%" (interptrm m))))
  (format g "(check-sat)~%")
  (format g "(exit)~%"))

(defun output-interp-smt (g ll sortl funl al)
  (output-interp-smt-real g ll sortl funl al)
  (when (> *verbosity* 99) (format t "====~%") (output-interp-smt-real *standard-output* ll sortl funl al) (format t "====~%")))

(defun output-interp-th0-real (g ll sortl funl al)
  (dolist (x sortl)
    (unless (or (assoc x *interptp* :test #'equal) (member x *unittp* :test #'equal))
      (format g "thf(c~d_tp,type,(c~d : $tType)).~%" x x)))
  (dolist (x funl)
    (unless (gethash (car x) *ret-unit*)
      (unless (or (assoc (car x) *interpfunc* :test #'equal)
		  (assoc (car x) *interpconst* :test #'equal))
	(format g "thf(c~d_tp,type,(c~d : " (car x) (car x))
	(setq i 0 p 0)
	(dolist (y (cadr x))
	  (incf i)
	  (if (member y *unittp* :test #'equal)
	      (setf (gethash (cons (car x) i) *arg-unit*) t)
	    (progn (incf p) (format g "(~d > " (interptp-th0 y)))))
	(format g "~d" (interptp-th0 (caddr x)))
	(dotimes (j p) (format g ")"))
	(format g ")).~%"))))
  (dolist (c *bcl*)
    (format g "thf(c~d,type,(c~d : $o)).~%" c c))
  (dolist (c *ccl*)
    (format g "thf(c~d,type,(c~d : $i)).~%" c c)) ; just use $i instead of int
  (let ((axc 0))
    (dolist (m al)
      (unless (trivial-after-interp m)
	(catch 'th0-fail
	  (format g "thf(ax~d,axiom,~d).~%" (incf axc) (interptrm-th0 m)))))))

(defun output-interp-th0 (g ll sortl funl al)
  (output-interp-th0-real g ll sortl funl al)
  (when (> *verbosity* 99) (format t "====~%") (output-interp-th0-real *standard-output* ll sortl funl al) (format t "====~%")))

(defun output-interp-sy-real (g ll sortl funl al)
  (dolist (l ll)
    (case (car l)
	  (set-info
	   (format g "(set-info")
	   (dolist (y (cdr l)) (format g " ~S" y))
	   (format g ")~%"))
	  (set-logic
	   (format g "(set-logic")
	   (dolist (y (cdr l))
	     (if (eq y 'UF)
		 (format g " UFLIA") ; extend to UFLIA to have Int
	       (format g " ~S" y)))
	   (format g ")~%"))
	  (t nil)))
  (dolist (x sortl)
    (unless (or (assoc x *interptp* :test #'equal) (member x *unittp* :test #'equal))
      (format g "(declare-sort ~d 0)~%" x)))
  (dolist (x funl)
    (unless (gethash (car x) *ret-unit*)
      (unless (or (assoc (car x) *interpfunc* :test #'equal)
		  (assoc (car x) *interpconst* :test #'equal))
	(format g "(synth-fun ~d (" (car x))
	(setq i 0)
	(when (> *verbosity* 4) (format t "synth-fun ~d~%" (car x)))
	(dolist (y (cadr x))
	  (incf i)
	  (when (> *verbosity* 4) (format t " ~d ~d ~d~%" i y (not (not (member y *unittp*)))))
	  (if (member y *unittp* :test #'equal)
	      (setf (gethash (cons (car x) i) *arg-unit*) t)
	    (format g " (X~d ~d)" i (interptp y))))
	(format g ") ~d)~%" (interptp (caddr x))))))
  (dolist (c *bcl*)
    (format g "(synth-fun ~d () Bool)~%" c))
  (dolist (c *ccl*)
    (format g "(synth-fun ~d () Int)~%" c))
  (dolist (m al)
    (unless (trivial-after-interp m)
      (format g "(constraint ~d)~%" (interptrm m))))
  (format g "(check-synth)~%"))

(defun output-interp-sy (g ll sortl funl al)
  (output-interp-sy-real g ll sortl funl al)
  (when (> *verbosity* 99) (format t "====~%") (output-interp-sy-real *standard-output* ll sortl funl al) (format t "====~%")))

(defun get-assert-prop-def-2 (f ml &optional (p t) cx)
  (if ml
      (or (get-assert-prop-def-1 f (car ml) p cx)
	  (get-assert-prop-def-2 f (cdr ml) p cx))
    nil))

(defun get-assert-prop-def-1 (f m &optional (p t) cx)
  (if (consp m)
      (case (car m)
	    (! (get-assert-prop-def-1 f (cadr m) p cx))
	    (not (get-assert-prop-def-1 f (cadr m) (not p) cx))
	    (and
	     (when p
	       (get-assert-prop-def-2 f (cdr m) p cx)))
	    (or
	     (unless p
	       (get-assert-prop-def-2 f (cdr m) p cx)))
	    (forall
	     (when p
	       (get-assert-prop-def-1 f (caddr m) p (append (mapcar #'car (cadr m)) cx))))
	    (exists
	     (unless p
	       (get-assert-prop-def-1 f (caddr m) p (append (mapcar #'car (cadr m)) cx))))
	    ((<=> =)
	     (when p
	       (let ((m1 (cadr m))
		     (m2 (caddr m)))
		 (if (and (consp m1) (equal (car m1) f) (distinct-bvars-p (cdr m1) cx)
			  (not (uninterp-fun-used-in-p m2)))
		     (list 'lambda (cdr m1) m2)
		   (when (and (consp m2) (equal (car m2) f) (distinct-bvars-p (cdr m2) cx)
			      (not (uninterp-fun-used-in-p f m1)))
		     (list 'lambda (cdr m2) m1))))))
	    (t
	     (when (and (equal (car m) f) (distinct-bvars-p (cdr m) cx))
	       (if p
		   (list 'lambda (cdr m) 'TRUE)
		 (list 'lambda (cdr m) 'FALSE)))))
    nil))
  
(defun get-assert-prop-def (f al)
  (if al
      (or (get-assert-prop-def-1 f (car al))
	  (get-assert-prop-def f (cdr al)))
    nil))
  
(defun get-assert-term-def-2 (f ml &optional (p t) cx)
  (if ml
      (or (get-assert-term-def-1 f (car ml) p cx)
	  (get-assert-term-def-2 f (cdr ml) p cx))
    nil))

(defun get-assert-term-def-1 (f m &optional (p t) cx)
  (if (consp m)
      (case (car m)
	    (! (get-assert-term-def-1 f (cadr m) p cx))
	    (not (get-assert-term-def-1 f (cadr m) (not p) cx))
	    (and
	     (when p
	       (get-assert-term-def-2 f (cdr m) p cx)))
	    (or
	     (unless p
	       (get-assert-term-def-2 f (cdr m) p cx)))
	    (forall
	     (when p
	       (get-assert-term-def-1 f (caddr m) p (append (mapcar #'car (cadr m)) cx))))
	    (exists
	     (unless p
	       (get-assert-term-def-1 f (caddr m) p (append (mapcar #'car (cadr m)) cx))))
	    (=
	     (when p
	       (let ((m1 (cadr m))
		     (m2 (caddr m)))
		 (if (and (consp m1) (equal (car m1) f) (distinct-bvars-p (cdr m1) cx)
			  (not (uninterp-fun-used-in-p m2)))
		     (list 'lambda (cdr m1) m2)
		   (when (and (consp m2) (equal (car m2) f) (distinct-bvars-p (cdr m2) cx)
			      (not (uninterp-fun-used-in-p f m1)))
		     (list 'lambda (cdr m2) m1))))))
	    (t nil))
    nil))
  
(defun get-assert-term-def (f al)
  (if al
      (or (get-assert-term-def-1 f (car al))
	  (get-assert-term-def f (cdr al)))
    nil))
  
(defun smtintfuncsynth-2 (sortposs fn ll sortl funl al)
  (setq *unittp* nil)
  (setq *interptp* nil)
  (setq *interpfunc* nil)
  (setq *interpconst* nil)
  (setq *ret-unit* (make-hash-table :test #'equal))
  (setq *arg-unit* (make-hash-table :test #'equal))
  (dolist (x sortposs)
    (if (eq (cdr x) 'UNIT)
	(push (car x) *unittp*)
      (push x *interptp*)))
  (dolist (x funl)
    (when (member (caddr x) *unittp* :test #'equal)
      (setf (gethash (car x) *ret-unit*) t))
    (dotimes (i (length (cadr x)))
      (when (member (nth i (cadr x)) *unittp* :test #'equal)
	(setf (gethash (cons (car x) (1+ i)) *arg-unit*) t))))
  (if *convert* ; just create sygus problem, don't try to solve it
      (let ((g (open (format nil "~d.converted.sy" fn) :direction :output :if-exists :supersede :if-does-not-exist :create)))
	(output-interp-sy g ll sortl funl al)
	(close g)
	(exit))
    (let ((g (open (format nil "~d.tmp.sy" fn) :direction :output :if-exists :supersede :if-does-not-exist :create)))
      (output-interp-sy g ll sortl funl al)
      (close g)
      (let ((r (call-cvc5 (format nil "~d.tmp.sy" fn))))
	(delete-file (format nil "~d.tmp.sy" fn))
	(when (and (consp r) (eq (car r) 'sygus-sat-probably))
	  (throw 'sat (list 'sat sortposs nil (cdr r))))))))

(defun smtintfuncsynth-1 (sortpossl fn ll sortl funl al)
  (if sortpossl
      (let ((r
	     (catch 'sat
	       (smtintfuncsynth-2 (car sortpossl) fn ll sortl funl al))))
	(if (and (consp r) (eq (car r) 'SAT))
	    r
	  (smtintfuncsynth-1 (cdr sortpossl) fn ll sortl funl al)))
    nil))

(defun smtintfuncsynth (fn)
  (let ((tm (get-universal-time)))
    (let ((r (catch 'sat (smtintfuncsynth-real fn))))
      (if (and (consp r) (eq (car r) 'SAT))
	  (if (cadddr r)
	      (format t "sat~%sortinterps:~%~S~%funcinterps:~%~S~%sygus result:~%~S~%" (cadr r) (caddr r) (cadddr r))
	    (format t "sat~%sortinterps:~%~S~%funcinterps:~%~S~%" (cadr r) (caddr r)))
	(if r
	    (format t "~S~%" r)
	  (format t "unknown~%"))))
    (format t "elapsed time: ~d~%" (- (get-universal-time) tm))
    ))

(defun smtintfuncsynth-real (fn)
  (multiple-value-bind
   (ll sortl funl al)
   (readsmt fn)
   (setq *infsort* (make-hash-table :test #'equal))
   (setq *nonunitsort* (make-hash-table :test #'equal))
   (setq *unittp* nil)
   (setq *interptp* nil)
   (setq *interpfunc* nil)
   (setq *interpconst* nil)
   (setq *retsort* (make-hash-table :test #'equal))
   (setq *argsorts* (make-hash-table :test #'equal))
   (setq *ret-unit* (make-hash-table :test #'equal))
   (setq *arg-unit* (make-hash-table :test #'equal))
   (dolist (c funl)
     (setf (gethash (car c) *retsort*) (caddr c))
     (setf (gethash (car c) *argsorts*) (cadr c)))
   (dolist (a al)
     (check-assert-nonunit a)
     (check-assert-infinite a))
   (let ((sortpartinterp nil)
	 (uninterpsorts nil))
     (dolist (x sortl)
       (if (gethash x *infsort*)
	   (push (cons x 'INT) sortpartinterp)
	 (push x uninterpsorts)))
     (when (> *verbosity* 4) (format t "uninterpsorts ~S~%" uninterpsorts))
     (dolist (x uninterpsorts)
       (if (gethash x *nonunitsort*)
	   (let ((sortposs (acons x 'BOOL sortpartinterp)))
	     (setq *unittp* nil)
	     (setq *interptp* sortposs)
	     (setq *interpfunc* nil)
	     (setq *interpconst* nil)
	     (setq *ret-unit* (make-hash-table :test #'equal))
	     (setq *arg-unit* (make-hash-table :test #'equal))
	     (dolist (x sortposs)
	       (if (eq (cdr x) 'UNIT)
		   (push (car x) *unittp*)
		 (push x *interptp*)))
	     (dolist (x funl)
	       (when (member (caddr x) *unittp* :test #'equal)
		 (setf (gethash (car x) *ret-unit*) t))
	       (dotimes (i (length (cadr x)))
		 (when (member (nth i (cadr x)) *unittp* :test #'equal)
		   (setf (gethash (cons (car x) (1+ i)) *arg-unit*) t))))
	     (let ((g (open (format nil "~d.tmp.smt2" fn) :direction :output :if-exists :supersede :if-does-not-exist :create)))
	       (output-interp-smt g ll sortl funl al)
	       (close g)
	       (let ((r (call-cvc5 (format nil "~d.tmp.smt2" fn))))
		 (when (> *verbosity* 9) (format t "sortposs ~d~%" r))
		 (delete-file (format nil "~d.tmp.smt2" fn))
		 (case r
		       (SAT (throw 'sat (list 'sat sortposs nil))) ; knows it's sat without generating function interps
		       (UNSAT
			(push (cons x 'INT) sortpartinterp))
		       (t
			(if *lash*
			    (let ((g (open (format nil "~d.tmp.th0.p" fn) :direction :output :if-exists :supersede :if-does-not-exist :create)))
			      (output-interp-th0 g ll sortl funl al)
			      (close g)
			      (let ((r (call-lash (format nil "~d.tmp.th0.p" fn))))
				(when (> *verbosity* 5) (format t "lash r ~d~%" r))
				(delete-file (format nil "~d.tmp.th0.p" fn))
				(case r
				      (UNSAT
				       (push (cons x 'INT) sortpartinterp))
				      (t
				       (push (cons x 'BOOL) sortpartinterp)))))
			  (push (cons x 'BOOL) sortpartinterp)))))))
	 (let ((sortposs (acons x 'UNIT sortpartinterp)))
	   (setq *unittp* nil)
	   (setq *interptp* sortposs)
	   (setq *interpfunc* nil)
	   (setq *interpconst* nil)
	   (setq *ret-unit* (make-hash-table :test #'equal))
	   (setq *arg-unit* (make-hash-table :test #'equal))
	   (dolist (x sortposs)
	     (if (eq (cdr x) 'UNIT)
		 (push (car x) *unittp*)
	       (push x *interptp*)))
	   (dolist (x funl)
	     (when (member (caddr x) *unittp* :test #'equal)
	       (setf (gethash (car x) *ret-unit*) t))
	     (dotimes (i (length (cadr x)))
	       (when (member (nth i (cadr x)) *unittp* :test #'equal)
		 (setf (gethash (cons (car x) (1+ i)) *arg-unit*) t))))
	   (let ((g (open (format nil "~d.tmp.smt2" fn) :direction :output :if-exists :supersede :if-does-not-exist :create)))
	     (output-interp-smt g ll sortl funl al)
	     (close g)
	     (let ((r (call-cvc5 (format nil "~d.tmp.smt2" fn))))
	       (when (> *verbosity* 9) (format t "sortposs ~d~%" r))
	       (delete-file (format nil "~d.tmp.smt2" fn))
	       (case r
		     (SAT (throw 'sat (list 'sat sortposs nil))) ; knows it's sat without generating function interps
		     (UNSAT
		      (let ((sortposs (acons x 'BOOL sortpartinterp)))
			(setq *unittp* nil)
			(setq *interptp* sortposs)
			(setq *interpfunc* nil)
			(setq *interpconst* nil)
			(setq *ret-unit* (make-hash-table :test #'equal))
			(setq *arg-unit* (make-hash-table :test #'equal))
			(dolist (x sortposs)
			  (if (eq (cdr x) 'UNIT)
			      (push (car x) *unittp*)
			    (push x *interptp*)))
			(dolist (x funl)
			  (when (member (caddr x) *unittp* :test #'equal)
			    (setf (gethash (car x) *ret-unit*) t))
			  (dotimes (i (length (cadr x)))
			    (when (member (nth i (cadr x)) *unittp* :test #'equal)
			      (setf (gethash (cons (car x) (1+ i)) *arg-unit*) t))))
			(let ((g (open (format nil "~d.tmp.smt2" fn) :direction :output :if-exists :supersede :if-does-not-exist :create)))
			  (output-interp-smt g ll sortl funl al)
			  (close g)
			  (let ((r (call-cvc5 (format nil "~d.tmp.smt2" fn))))
			    (when (> *verbosity* 9) (format t "sortposs ~d~%" r))
			    (delete-file (format nil "~d.tmp.smt2" fn))
			    (case r
				  (SAT (throw 'sat (list 'sat sortposs nil))) ; knows it's sat without generating function interps
				  (UNSAT
				   (push (cons x 'INT) sortpartinterp))
				  (t
				   (if *lash*
				       (let ((g (open (format nil "~d.tmp.th0.p" fn) :direction :output :if-exists :supersede :if-does-not-exist :create)))
					 (output-interp-th0 g ll sortl funl al)
					 (close g)
					 (let ((r (call-lash (format nil "~d.tmp.th0.p" fn))))
					   (when (> *verbosity* 5) (format t "lash r ~d~%" r))
					   (delete-file (format nil "~d.tmp.th0.p" fn))
					   (case r
						 (UNSAT
						  (push (cons x 'INT) sortpartinterp))
						 (t
						  (push (cons x 'BOOL) sortpartinterp)))))
				     (push (cons x 'BOOL) sortpartinterp))))))))
		     (t
		      (if *lash*
			  (let ((g (open (format nil "~d.tmp.th0.p" fn) :direction :output :if-exists :supersede :if-does-not-exist :create)))
			    (output-interp-th0 g ll sortl funl al)
			    (close g)
			    (let ((r (call-lash (format nil "~d.tmp.th0.p" fn))))
			      (when (> *verbosity* 5) (format t "lash r ~d~%" r))
			      (delete-file (format nil "~d.tmp.th0.p" fn))
			      (case r
				    (UNSAT
				     (let ((sortposs (acons x 'BOOL sortpartinterp)))
				       (setq *unittp* nil)
				       (setq *interptp* sortposs)
				       (setq *interpfunc* nil)
				       (setq *interpconst* nil)
				       (setq *ret-unit* (make-hash-table :test #'equal))
				       (setq *arg-unit* (make-hash-table :test #'equal))
				       (dolist (x sortposs)
					 (if (eq (cdr x) 'UNIT)
					     (push (car x) *unittp*)
					   (push x *interptp*)))
				       (dolist (x funl)
					 (when (member (caddr x) *unittp* :test #'equal)
					   (setf (gethash (car x) *ret-unit*) t))
					 (dotimes (i (length (cadr x)))
					   (when (member (nth i (cadr x)) *unittp* :test #'equal)
					     (setf (gethash (cons (car x) (1+ i)) *arg-unit*) t))))
				       (let ((g (open (format nil "~d.tmp.smt2" fn) :direction :output :if-exists :supersede :if-does-not-exist :create)))
					 (output-interp-smt g ll sortl funl al)
					 (close g)
					 (let ((r (call-cvc5 (format nil "~d.tmp.smt2" fn))))
					   (when (> *verbosity* 9) (format t "sortposs ~d~%" r))
					   (delete-file (format nil "~d.tmp.smt2" fn))
					   (case r
						 (SAT (throw 'sat (list 'sat sortposs nil))) ; knows it's sat without generating function interps
						 (UNSAT
						  (push (cons x 'INT) sortpartinterp))
						 (t
						  (if *lash*
						      (let ((g (open (format nil "~d.tmp.th0.p" fn) :direction :output :if-exists :supersede :if-does-not-exist :create)))
							(output-interp-th0 g ll sortl funl al)
							(close g)
							(let ((r (call-lash (format nil "~d.tmp.th0.p" fn))))
							  (when (> *verbosity* 5) (format t "lash r ~d~%" r))
							  (delete-file (format nil "~d.tmp.th0.p" fn))
							  (case r
								(UNSAT
								 (push (cons x 'INT) sortpartinterp))
								(t
								 (push (cons x 'BOOL) sortpartinterp)))))
						    (push (cons x 'BOOL) sortpartinterp))))))))
				    (t
				     (push (cons x 'UNIT) sortpartinterp)))))
			(push (cons x 'UNIT) sortpartinterp)))))))))
     (when (> *verbosity* 5)
       (format t "al: ~S~%sortpartinterp: ~S~%*unittp*: ~S~%" al sortpartinterp *unittp*))
;     (setq *sortpartinterp* sortpartinterp) (break)
     (smtintfuncsynth-1 (list sortpartinterp) fn ll sortl funl al))))

