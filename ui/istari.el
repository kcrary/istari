;; Assumes that the istari-root contains the path to the Istari root directory.

(require 'seq "seq")

(defvar ist-running 'nil)



(defcustom istari-binary 
  (concat istari-root "/ui/bin/istarisrv-heapimg")
  "Location of the Istari binary.")

(defcustom istari-nolib-binary 
  (concat istari-root "/ui/bin/istarisrv-nolib-heapimg")
  "Location of the Istari binary (without preloaded libraries).")

(defcustom istari-load-libraries t
  "Whether to preload the Istari libraries.")

(defvar ist-output-frame-top 0)
(defvar ist-output-frame-left 638)
(defvar ist-output-frame-height 75)
(defvar ist-output-frame-width 100)

(defcustom istari-indent-increment 2 "Code indentation increment.")

(require 'iml-mode (concat istari-root "/ui/iml.el"))

(defconst istari-mode-map (make-sparse-keymap))
(set-keymap-parent istari-mode-map iml-mode-map)
(define-key istari-mode-map "\C-c\C-p" 'istari-prev)
(define-key istari-mode-map "\C-c\C-u" 'istari-prev)  ; ProofGeneral compatibility
(define-key istari-mode-map [f4] 'istari-prev)
(define-key istari-mode-map "\C-c\C-n" 'istari-next)
(define-key istari-mode-map [f5] 'istari-next)
(define-key istari-mode-map "\C-c\C-m" 'istari-goto)
(define-key istari-mode-map [3 C-return] 'istari-goto)
(define-key istari-mode-map "\C-ci" 'istari-interject)
(define-key istari-mode-map (kbd "C-c C-.") 'istari-goto-marker)
(define-key istari-mode-map "\C-c\C-c" 'istari-interrupt)
(define-key istari-mode-map "\C-c\C-r" 'istari-read-only)
(define-key istari-mode-map [f9] 'istari-step)
(define-key istari-mode-map [f10] 'istari-run)

(define-key istari-mode-map "\C-cpa" 'istari-adjust)
(define-key istari-mode-map "\C-cpt" 'istari-terminate)
(define-key istari-mode-map "\C-cpl" 'istari-toggle-load-libraries)

(define-key istari-mode-map "\C-c\C-d" 'istari-detail)
(define-key istari-mode-map "\C-cs" 'istari-show)
(define-key istari-mode-map "\C-cS" 'istari-show-full)
(define-key istari-mode-map "\C-cra" 'istari-report-all)
(define-key istari-mode-map "\C-crm" 'istari-report-module)
(define-key istari-mode-map "\C-crs" 'istari-report-show)
(define-key istari-mode-map "\C-crt" 'istari-report-type)
(define-key istari-mode-map "\C-cci" 'istari-show-implicits)
(define-key istari-mode-map "\C-ccs" 'istari-show-substitutions)


(defun istari-mode ()
  "Major mode for Istari proof editing.

\\{istari-mode-map}"
  (interactive)
  (kill-all-local-variables)
  (use-local-map istari-mode-map)
  (setq mode-name "Istari")
  (setq major-mode 'istari-mode)
  (set-syntax-table iml-mode-syntax-table)
  (setq indent-tabs-mode nil)
  (make-local-variable 'iml-indent-increment)
  (setq iml-indent-increment istari-indent-increment)
  (run-hooks 'istari-mode-hook))


;; Most of this is just trying to keep the point at the end, if it's already there.
;; I later decided I didn't want this behavior.
;; (defun ist-buf-print (buf str)
;;   (with-current-buffer buf
;;     (let* ((bufatend (= (point) (point-max)))
;;            (win (get-buffer-window buf t))
;;            (winatend (if (= (window-point win) (point-max)) win)))
;;       (save-excursion
;;         (goto-char (point-max))
;;         (insert str))
;;       (let ((m (point-max)))
;;         (if bufatend (goto-char m))
;;         (if winatend
;;             (set-window-point winatend m))))))

(defun ist-buf-print (str)
  (with-current-buffer ist-output-buffer
    (save-excursion
      (goto-char (point-max))
      (insert str))
    (if (not (and ist-output-window (window-live-p ist-output-window)))
        (progn
          (ist-frame)
          (setq ist-output-window (get-buffer-window ist-output-buffer t))))
    (set-window-point ist-output-window (point-max))))

(defvar ist-overlay)
(defvar ist-cursor)
(defvar ist-read-only-curr)

;; borrowed this code from ProofGeneral
(defun ist-read-only-hook (overlay after start end &optional len)
  (unless (or inhibit-read-only (= (overlay-start overlay) (overlay-end overlay)))
    (error "Read-only region")))
(add-to-list 'debug-ignored-errors "Read-only region")

(defun ist-overlay-read-only ()
  (setq ist-read-only-curr t)
  (overlay-put ist-overlay 'modification-hooks '(ist-read-only-hook))
  (overlay-put ist-overlay 'insert-in-front-hooks '(ist-read-only-hook)))

(defun ist-overlay-read-write ()
  (setq ist-read-only-curr nil)
  (overlay-put ist-overlay 'modification-hooks nil)
  (overlay-put ist-overlay 'insert-in-front-hooks nil))

(defun ist-get-cursor ()
  (overlay-start ist-cursor))

(defun ist-set-cursor (pos)
  (if (= (overlay-start ist-cursor) (overlay-end ist-cursor))
      (move-overlay ist-cursor pos pos)
    (move-overlay ist-cursor pos (overlay-end ist-cursor)))
  (move-overlay ist-overlay (point-min) pos))

(defun ist-cursor-working ()
  (if (display-graphic-p)
      (overlay-put ist-cursor
                   'before-string
                   (propertize
                    "x" 'display '(left-fringe filled-square default)))
    (overlay-put ist-cursor
                 'before-string "[working]\n")))
    
(defun ist-cursor-ready ()
  (if (display-graphic-p)
      (overlay-put ist-cursor
                   'before-string
                   (propertize
                    "x" 'display '(left-fringe right-triangle default)))
    (overlay-put ist-cursor
                 'before-string "[ready]\n")))

(defun ist-cursor-partial ()
  (if (display-graphic-p)
      (overlay-put ist-cursor
                   'before-string
                   (propertize
                    "x" 'display '(left-fringe left-triangle default)))
    (overlay-put ist-cursor
                 'before-string "[partial]\n")))
    
(defvar ist-partial)

(defun ist-cursor-ready-or-partial ()
  (if ist-partial
      (ist-cursor-partial)
    (ist-cursor-ready)))


(defvar ist-rewind-detected)

(defun ist-move-marker (n)
  (save-excursion
    (goto-char (ist-get-cursor))
    (forward-line n)
    (ist-set-cursor (point))))

(defvar ist-sending nil)

(defun ist-escape (str)
  (let ((code (elt str 0)))
    (cond
     ((eq code ?r)
      (if ist-sending
          (setq ist-partial nil)
        (ist-cursor-ready))
      (ist-signal))
     ((eq code ?p)
      (if ist-sending
          (setq ist-partial t)
        (ist-cursor-partial))
      (ist-signal))
     ((eq code ?c)
      (ist-move-marker (- (string-to-number (substring str 1))))
      (setq ist-rewind-detected t))
     ((eq code ?m)
      (message "%s" (substring str 1)))
     ((eq code ?b)
      (ding)))))

(defun ist-signal ()
  (if ist-sending
      (ist-send-loop)))

(defvar ist-output-buffer)
(defvar ist-output-window)
(defvar ist-output-frame nil)
(defvar ist-output-mode 'ist-output-normal)
(defvar ist-rewind-detected nil)
(defvar ist-retained-output "")

(defun ist-output-escape (str)
  (let* ((str (concat ist-retained-output str))
         (pos (seq-position str 2)))
    (if pos
        (progn
          (setq ist-retained-output "")
          (setq ist-output-mode 'ist-output-normal)
          (ist-escape (substring str 0 pos))
          (ist-output-normal (substring str (+ pos 1))))
      (setq ist-retained-output str))))

(defun ist-output-normal (str)
  (let ((pos (seq-position str 1)))
    (cond
     (pos (progn
            (ist-buf-print (substring str 0 pos))
            (setq ist-retained-output "")
            (setq ist-output-mode 'ist-output-escape)
            (ist-output-escape (substring str (+ pos 1)))))
     (t (ist-buf-print str)))))

;; filter function for handling istari output
(defun ist-ml-output (proc str)
  (funcall ist-output-mode str))

(defvar ist-source-buffer)
(defvar ist-ml-proc)

(defun ist-frame ()
  "Create Istari frame."
  (interactive)
  (if (display-graphic-p)
      (if (and
           (frame-live-p ist-output-frame)
           (eq (window-buffer (frame-root-window ist-output-frame)) ist-output-buffer))
          ()
        (let
            ((current-frame (selected-frame)))
          (setq ist-output-frame (make-frame))
          (set-frame-parameter ist-output-frame 'top ist-output-frame-top)
          (set-frame-parameter ist-output-frame 'left ist-output-frame-left)
          (set-frame-parameter ist-output-frame 'height ist-output-frame-height)
          (set-frame-parameter ist-output-frame 'width ist-output-frame-width)
          (select-frame ist-output-frame)
          (switch-to-buffer ist-output-buffer)
          (goto-char (point-max))
          (setq-local scroll-conservatively 101)
          (select-frame-set-input-focus current-frame)))
    (selected-frame)))
    
(defun istari-start ()
  "Start Istari process."
  (interactive)
  (if ist-running
      (error "Istari already running.")
    (setq ist-source-buffer (current-buffer))
    (setq ist-cursor (make-overlay (point-min) (point-min)))
    (overlay-put ist-cursor 'face 'highlight)
    (ist-cursor-ready)
    (setq ist-overlay (make-overlay (point-min) (point-min)))
    (ist-overlay-read-only)
    (setq ist-running t)
    (setq ist-sending nil)
    (setq ist-output-buffer (get-buffer-create "*istari*"))
    (setq ist-output-window nil)
    (ist-frame)
    (setq ist-ml-proc 
          (start-process "ist-ml" "*subordinate istari process*" "sml" 
                         (concat "@SMLload=" 
                                 (if istari-load-libraries istari-binary istari-nolib-binary))))
    (set-process-filter (get-process "ist-ml") 'ist-ml-output)
    ;; make sure the input is flushed
    (accept-process-output ist-ml-proc)))

(defun istari-terminate ()
  "Terminate Istari process."
  (interactive)
  (unless ist-running
    (error "Istari not running"))
  (delete-overlay ist-cursor)
  (delete-overlay ist-overlay)
  (let ((buf (process-buffer ist-ml-proc)))
    (delete-process ist-ml-proc)
    (kill-buffer buf))
  (setq ist-running nil)
  (message "Istari terminated"))

(defun ist-send-string (str)
  (process-send-string ist-ml-proc str))

(defun line-start-position (pos)
  (save-excursion
    (goto-char pos)
    (beginning-of-line)
    (point)))

(defun next-line-position (pos)
  (save-excursion
    (goto-char pos)
    (forward-line)
    (point)))

(defun ist-not-yet ()
  (ding)
  (message "Not ready"))

(defun istari-interject (str)
  "Send out-of-band code to Istari."
  (interactive "MCode: ")
  (unless ist-running
    (istari-start))
  (if ist-sending
      (ist-not-yet)
    (ist-send-string (concat "\^B" str "\n"))))

(defun ist-advance ()
  (with-current-buffer ist-source-buffer
    (let* ((start (ist-get-cursor))
           (end (next-line-position start)))
      (ist-set-cursor end)
      (ist-send-string (buffer-substring start end)))))

(defun ist-send-loop ()
  (let
      ((pos (ist-get-cursor)))
    (if (or
         ist-rewind-detected
         (>= pos (overlay-end ist-cursor)))
        (progn
          (setq ist-sending nil)
          (move-overlay ist-cursor pos pos)
          (ist-cursor-ready-or-partial)
          (ist-send-string "\^E\n"))
      (ist-advance))))

(defun ist-send (pos)
  (let ((pos (line-start-position pos))
        (cur (ist-get-cursor)))
    (move-overlay ist-cursor cur (max pos cur))
    (if ist-sending
        nil
      (setq ist-sending t)
      (setq ist-rewind-detected nil)
      (ist-cursor-working)
      (ist-send-loop))))

(defun istari-next ()
  "Send next line to Istari."
  (interactive)
  (unless ist-running
    (istari-start))
  (if (eq (current-buffer) ist-source-buffer)
      (let* ((start (or (and ist-sending (overlay-end ist-cursor)) (ist-get-cursor)))
             (end (next-line-position start)))
        (if (= start end) ; end of buffer
            (ding)
          (ist-send end)))
    (error "Istari running in another buffer.")))

(defun ist-rewind (pos)
  (if ist-sending
      (ist-not-yet)
    (let*
        ((pos (line-start-position pos))
         (n (- (line-number-at-pos (ist-get-cursor))
               (line-number-at-pos pos))))
      (when (> n 0)
        (ist-send-string (concat "\^A" (number-to-string n) "\n"))))))

(defun istari-goto (pos)
  "Send code to Istari or rewind Istari state."
  (interactive "d")
  (unless ist-running
    (istari-start))
  (if (eq (current-buffer) ist-source-buffer)
      (if (>= pos (ist-get-cursor))
          (ist-send pos)
        (ist-rewind pos))
    (error "Istari running in another buffer.")))

(defun istari-adjust (pos)
  "Set the UI's position."
  (interactive "d")
  (unless ist-running
    (error "Istari not running."))
  (if (eq (current-buffer) ist-source-buffer)
      (if ist-sending
          (ist-not-yet)
        (ist-set-cursor (line-start-position pos)))
    (error "Istari running in another buffer.")))

(defun istari-prev ()
  "Rewind UI to previous line."
  (interactive)
  (unless ist-running
    (error "Istari not running."))
  (if (eq (current-buffer) ist-source-buffer)
      (if ist-sending
          (ist-not-yet)
        (ist-rewind (save-excursion
                         (goto-char (ist-get-cursor))
                         (forward-line -1)
                         (point))))
    (error "Istari running in another buffer.")))

(defun istari-goto-marker ()
  "Move to Istari input marker."
  (interactive)
  (unless ist-running
    (error "Istari not running."))
  (if (not (eq (current-buffer) ist-source-buffer))
      (switch-to-buffer ist-source-buffer))
  (goto-char (ist-get-cursor)))

(defun istari-interrupt ()
  "Interrupt Istari process."
  (interactive)
  (unless ist-running
    (error "Istari not running."))
  (interrupt-process ist-ml-proc)
  (ist-cursor-ready)
  (setq ist-sending nil)
  (move-overlay ist-cursor (ist-get-cursor) (ist-get-cursor))
  (ist-send-string "RecoverRepl.recover ();\n"))

(defun istari-restart ()
  "Restart Istari process."
  (interactive)
  (if ist-running
      (progn
        (istari-terminate)
        (istari-start))
    (istari-start)))

(defun istari-read-only ()
  "Toggle read-only status of checked region."
  (interactive)
  (if ist-read-only-curr
      (ist-overlay-read-write)
    (ist-overlay-read-only)))

(defun istari-step ()
  "Single-step the prover."
  (interactive)
  (istari-interject "Debugger.step ();"))

(defun istari-run ()
  "Resume the prover."
  (interactive)
  (istari-interject "Debugger.run ();"))

(defun istari-toggle-load-libraries ()
  "Toggle loading the Istari library."
  (interactive)
  (setq istari-load-libraries (not istari-load-libraries))
  (if istari-load-libraries
      (message "Loading libraries enabled")
    (message "Loading libraries disabled")))


;; Utilities

(defun istari-detail ()
  "Request detail from the prover."
  (interactive)
  (istari-interject "Prover.detail ();"))

(defun istari-show ()
  "Show the current prover state."
  (interactive)
  (istari-interject "Prover.show ();"))

(defun istari-show-full ()
  "Show the current full prover state."
  (interactive)
  (istari-interject "Prover.showFull ();"))

(defun istari-report-all ()
  "List the entire proof environment."
  (interactive)
  (istari-interject "Report.showAll ();"))

(defun istari-report-module (str)
  "List the contents of a module."
  (interactive "MModule: ")
  (istari-interject (concat "Report.showModule (parseLongident /" str "/);")))

(defun istari-report-show (str)
  "Report the definition and type of a constant."
  (interactive "MConstant: ")
  (istari-interject (concat "Report.show (parseLongident /" str "/);")))
  
(defun istari-report-type (str)
  "Report the type of a constant."
  (interactive "MConstant: ")
  (istari-interject (concat "Report.showType (parseLongident /" str "/);")))

(defun istari-show-implicits ()
  "Toggle showing implicit arguments."
  (interactive)
  (istari-interject "Show.showImplicits := not (!Show.showImplicits); if !Show.showImplicits then print \"Display of implicit arguments enabled.\\n\" else print \"Display of implicit arguments disabled.\\n\";"))

(defun istari-show-substitutions ()
  "Toggle showing substitutions."
  (interactive)
  (istari-interject "Show.showSubstitutions := not (!Show.showSubstitutions); if !Show.showSubstitutions then print \"Display of evar substitutions enabled.\\n\" else print \"Display of evar substitutions disabled.\\n\";"))

(run-hooks 'istari-hook)
