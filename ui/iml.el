;; iml.el  Major mode for editing iml.
;; Minimalistic (ie, predictable)

(defvar iml-indent-increment 3 "*Iml indentation increment.")
(defvar iml-ignore-leading-bar t "*Whether indentation should ignore leading bars.")
(defvar iml-align-eol-delimeter t "*Whether indentation should align with a delimiter at the end of a line.")

(defvar iml-mode-syntax-table nil
  "Syntax table used while in IML mode.")

(if iml-mode-syntax-table
    ()
  (setq iml-mode-syntax-table (make-syntax-table))
  (modify-syntax-entry ?/ "$" iml-mode-syntax-table)
  (modify-syntax-entry ?\\ "$" iml-mode-syntax-table))

(defvar iml-mode-map () "Keymap used while in Iml mode.")

(defun define-iml-bindings-into-map (keymap)
  (define-key keymap "\t" 'iml-tab)
  (define-key keymap (kbd "<C-tab>") 'iml-backtab)
  (define-key keymap "\C-c\C-l" 'iml-set-indent)
  (define-key keymap "\M-i" 'iml-repeat-indent)
  (define-key keymap "\M-|" 'iml-electric-bar)
  (define-key keymap "\C-\M-i" 'indent-relative))

(if iml-mode-map
    ()
  (setq iml-mode-map (make-sparse-keymap))
  (define-iml-bindings-into-map iml-mode-map))

(defun iml-mode ()
  "Major mode for editing iml."
  (interactive)
  (kill-all-local-variables)
  (use-local-map iml-mode-map)
  (setq mode-name "IML")
  (setq major-mode 'iml-mode)
  (set-syntax-table iml-mode-syntax-table)
  (setq indent-tabs-mode nil)
  (run-hooks 'iml-mode-hook))

(defun iml-bindings ()
  "Set key bindings as for IML mode."
  (interactive)
  (local-set-key "\t" 'iml-tab)
  (local-set-key (kbd "<C-tab>") 'iml-backtab)
  (local-set-key "\C-c\C-s" 'iml-set-indent)
  (local-set-key "\M-i" 'iml-repeat-indent)
  (local-set-key "\M-|" 'iml-electric-bar)
  (local-set-key "\C-\M-i" 'tab-to-tab-stop))


;; delimited

(defun iml-backward-delimited ()
  (catch 'exit
    (while t  ;; No tail recursion elimination in Elisp.
      (if (bobp)
	  (error "No matching delimeter")
	(backward-char)
	(cond
	 ((= (char-syntax (char-after)) ?\()
	  (throw 'exit t))
	 ((= (char-syntax (char-after)) ?\))
	  (iml-backward-delimited)))))))


;; newline

(defun iml-backward-to-newline ()
  (catch 'exit
    (while t  ;; No tail recursion elimination in Elisp.
      (if (bolp)
	  (throw 'exit t)
	(backward-char)
	(cond
	 ((= (char-syntax (char-after)) ?\()
	  (forward-char)
	  (throw 'exit nil))
	 ((= (char-syntax (char-after)) ?\))
	  (iml-backward-delimited)))))))

(defun iml-backward-to-literal-newline ()
  (catch 'exit
    (while t  ;; No tail recursion elimination in Elisp.
      (if (bolp)
	  (throw 'exit t)
	(backward-char)
	(cond
	 ((= (char-syntax (char-after)) ?\))
	  (iml-backward-delimited)))))))



;; indentation

(defun iml-backward-to-indentation ()
  (if (bobp)
      nil
    (if (iml-backward-to-newline)
	;; at beginning of line
	(progn
	  (if iml-ignore-leading-bar
	      (skip-chars-forward " \t|")
	     (skip-chars-forward " \t"))
	  (if (not (eolp))
	      ;; nonempty line, good
	      t
	    ;; this line is empty, find a better one
	    (beginning-of-line)
	    (if (bobp)
		;; start of buffer, we won't do any better
		t
	      (backward-char)
	      (iml-backward-to-indentation))))
      ;; just after delimiter
      (let
	  ((p (point)))
	(skip-chars-forward " \t")
	(if (not (eolp))
	    ;; delimiter not at end of line
	    t
	  ;; special case! delimiter is at end of line, restore the delimiter's position
	  (goto-char 
	   (if iml-align-eol-delimeter
	       (- p 1)
	     p)))))))

(defun iml-indentation ()
  (save-excursion
    (beginning-of-line)
    (if (bobp)
	0
      (backward-char)
      (iml-backward-to-indentation)
      (current-column))))


;; tab

(defun back-to-indentation* ()
  (let
      ((p (point)))
    (back-to-indentation)
    (if (eolp)
	;; line is blank, restore previous position
	(goto-char p))))

(defun iml-tab ()
  "Advance indentation of current line of iml."
  (interactive)
  (back-to-indentation*)
  (let
      ((i (iml-indentation))
       (j (current-column)))
    (delete-horizontal-space)
    (if (< j i)
	(indent-to i)
      (indent-to (+ j iml-indent-increment)))))

(defun iml-backtab ()
  "Reduce indentation of current line of iml."
  (interactive)
  (back-to-indentation*)
  (let
      ((i (iml-indentation))
       (j (current-column)))
    (delete-horizontal-space)
    (if (> j i)
	(indent-to i)
      (indent-to (- j iml-indent-increment)))))

(defun iml-indent-to-literal-newline ()
  "Indent to previous line, passing through open parentheses."
  (interactive)
  (let
      ((i (save-excursion
            (while
                (progn
                  (beginning-of-line)
                  (if (bobp)
                      nil
                    (backward-char)
                    (iml-backward-to-literal-newline)
                    (skip-chars-forward " \t")
                    (eolp))))
            (if (bobp)
                0
              (current-column)))))
    (delete-horizontal-space)
    (indent-to i)))


;; block indent

(setq iml-prior-indent nil)

(defun iml-set-indent ()
  "Set prior indentation of iml block."
  (interactive)
  (setq iml-prior-indent (current-column))
  (message "Prior indentation set"))

(defun iml-repeat-indent ()
  "Repeat indentation of iml block."
  (interactive)
  (if iml-prior-indent
      (progn
	(setq iml-indent-delta (- (current-column) iml-prior-indent))
	(setq iml-prior-indent nil)))
  (forward-line 1)
  (back-to-indentation)
  (let
      ((j (current-column)))
    (delete-horizontal-space)
    (indent-to (+ j iml-indent-delta))))


;; bar

(defun iml-backward-to-bar ()
  (catch 'exit
    (while t  ;; No tail recursion in Elisp.
      (if (bobp)
	  (throw 'exit nil)
	(backward-char)
	(cond
	 ((= (char-after) ?\|)
	  (throw 'exit t))
	 ((= (char-syntax (char-after)) ?\()
	  (forward-char)
	  (throw 'exit nil))
	 ((= (char-syntax (char-after)) ?\))
	  (iml-backward-delimited)))))))

(defun iml-bar-indentation ()
  (save-excursion
    (if (iml-backward-to-bar)
	(current-column)
      (+ (current-column) (- iml-indent-increment 2)))))

(defun iml-electric-bar ()
  "Indent to matching bar."
  (interactive)
  (delete-horizontal-space)
  (if (not (bolp))
      (insert "\n"))
  (indent-to (iml-bar-indentation))
  (insert "| "))


;; insert-indented-line

(defun insert-indented-line ()
  "Insert line, indented to current column."
  (interactive)
  (let
      ((i (current-column)))
    (insert "\n")
    (indent-to i)))


(run-hooks 'iml-hook)

(provide 'iml-mode)
