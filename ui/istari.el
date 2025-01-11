;; Assumes that the istari-root contains the path to the Istari root directory.

(require 'seq "seq")

(defvar ist-running 'nil)



(defcustom istari-binaries
  (list
   (cons "Libraries disabled." (concat istari-root "/ui/bin/istarisrv-nolib-heapimg"))
   (cons "Libraries enabled." (concat istari-root "/ui/bin/istarisrv-heapimg")))
  "Locations of the Istari binaries.")

(defvar istari-binary-index 0)
(defvar istari-binary (cdar (last istari-binaries)))

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
(define-key istari-mode-map [C-return] 'istari-goto)
(define-key istari-mode-map "\C-cx" 'istari-interject)
(define-key istari-mode-map (kbd "C-c C-.") 'istari-goto-marker)
(define-key istari-mode-map "\C-c\C-c" 'istari-interrupt)
(define-key istari-mode-map "\C-c\C-r" 'istari-read-only)
(define-key istari-mode-map [f9] 'istari-step)
(define-key istari-mode-map [f10] 'istari-run)

(define-key istari-mode-map "\C-cpt" 'istari-terminate)
(define-key istari-mode-map "\C-cpl" 'istari-cycle-binaries)

(define-key istari-mode-map "\C-c\C-d" 'istari-detail)
(define-key istari-mode-map "\C-cs" 'istari-show)
(define-key istari-mode-map "\C-cS" 'istari-show-full)
(define-key istari-mode-map "\C-cra" 'istari-report-all)
(define-key istari-mode-map "\C-crm" 'istari-report-module)
(define-key istari-mode-map "\C-crs" 'istari-report-show)
(define-key istari-mode-map "\C-crf" 'istari-report-search)
(define-key istari-mode-map "\C-crs" 'istari-report-show)
(define-key istari-mode-map "\C-crt" 'istari-report-type)
(define-key istari-mode-map "\C-cia" 'istari-insert-application)
(define-key istari-mode-map "\C-cii" 'istari-insert-intros)
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

(defvar ist-overlay) ; used to designate the read-only region
(defvar ist-cursor)  ; working region visible to the user
(defvar ist-read-only-curr)

;; borrowed this code from ProofGeneral
;; it still allows modification by undo; I don't know how to prevent that
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

(defun ist-set-cursor-start (pos)
  (if (= (overlay-start ist-cursor) (overlay-end ist-cursor))
      (progn
        (move-overlay ist-cursor pos pos)
        (move-overlay ist-overlay (point-min) pos))
    (move-overlay ist-cursor pos (overlay-end ist-cursor))))

(defun ist-set-cursor-end (pos)
  (move-overlay ist-cursor (overlay-start ist-cursor) pos)
  (move-overlay ist-overlay (point-min) pos))

(defun ist-minimize-cursor ()
  (let
      ((pos (overlay-start ist-cursor)))
    (move-overlay ist-cursor pos pos)
    (move-overlay ist-overlay (point-min) pos)))

(defvar ist-working nil)

(defun ist-cursor-working ()
  (setq ist-working t)
  (if (display-graphic-p)
      (overlay-put ist-cursor
                   'before-string
                   (propertize
                    "x" 'display '(left-fringe filled-square default)))
    (overlay-put ist-cursor
                 'before-string "[working]\n")))
    
(defun ist-cursor-ready ()
  (setq ist-working nil)
  (if (display-graphic-p)
      (overlay-put ist-cursor
                   'before-string
                   (propertize
                    "x" 'display '(left-fringe right-triangle default)))
    (overlay-put ist-cursor
                 'before-string "[ready]\n")))

(defun ist-cursor-partial ()
  (setq ist-working nil)
  (if (display-graphic-p)
      (overlay-put ist-cursor
                   'before-string
                   (propertize
                    "x" 'display '(left-fringe left-triangle default)))
    (overlay-put ist-cursor
                 'before-string "[partial]\n")))
    
(defun ist-line-number-to-pos (line)
  (with-current-buffer ist-source-buffer
    (save-excursion
      (goto-char (point-min))
      (forward-line (- line 1))
      (point))))

(defvar ist-permit-insert nil)

(defun ist-escape (str)
  (let ((code (elt str 0)))
    (cond
     ((eq code ?c)
      (ist-set-cursor-start (ist-line-number-to-pos (string-to-number (substring str 1)))))
     ((eq code ?r)
      (ist-cursor-ready))
     ((eq code ?p)
      (ist-cursor-partial))
     ((eq code ?w)
      (ist-cursor-working))
     ((eq code ?f)
      (ist-minimize-cursor)
      (ist-send-string "\^F\n"))
     ((eq code ?m)
      (message "%s" (substring str 1)))
     ((eq code ?b)
      (ding))
     ((eq code ?i)
      (if ist-permit-insert
          (progn
            (condition-case err
                (insert (substring str 1))
              (error (progn 
                       (ding)
                       (message (format "Error inserting: %s" err)))))
            (setq ist-permit-insert nil)))))))

(defvar ist-output-buffer)
(defvar ist-output-window)
(defvar ist-output-frame nil)

(defvar ist-output-mode-normal t)
(defvar ist-retained-output nil)

;; filter function for handling istari output
(defun ist-ml-output (proc str)
  (if ist-retained-output
      (progn
        (setq str (concat ist-retained-output str))
        (setq ist-retained-output nil)))
  (while (not (string= str ""))
    (if ist-output-mode-normal
        (let ((pos (seq-position str 1)))
          (if pos
              (progn
                (ist-buf-print (substring str 0 pos))
                (setq ist-output-mode-normal nil)
                (setq str (substring str (+ pos 1))))
            (ist-buf-print str)
            (setq str "")))
      (let
          ((pos (seq-position str 2)))
        (if pos
            (progn
              (ist-escape (substring str 0 pos))
              (setq ist-output-mode-normal t)
              (setq str (substring str (+ pos 1))))
          (setq ist-retained-output str)
          (setq str ""))))))

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
    (setq ist-output-mode-normal t)
    (setq ist-retained-output nil)
    (ist-frame)
    (setq ist-ml-proc 
          (let 
              ; connect using a pipe (Emacs has a bug with large sends using ptys)
              ((process-connection-type nil)) 
            (start-process "ist-ml" "*subordinate istari process*" "sml" 
                           (concat "@SMLload=" istari-binary))))
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
  (if ist-working
      (ist-not-yet)
    (ist-send-string (concat "\^B" str "\n"))))

(defun ist-send (pos)
  (with-current-buffer ist-source-buffer
    (let ((new (line-start-position pos))
          (cur (overlay-end ist-cursor)))
      (if (> new cur)
          (progn
            (ist-set-cursor-end new)
            (process-send-region ist-ml-proc cur new)
            (ist-send-string "\^E\n"))))))

(defun ist-rewind (pos)
  (with-current-buffer ist-source-buffer
    (let
        ((start (overlay-start ist-cursor))
         (end (overlay-end ist-cursor))
         (pos (line-start-position pos)))
      (if (or (< start end) (> pos end))
          (ding)
        (ist-send-string (concat "\^A" (number-to-string (line-number-at-pos (line-start-position pos))) "\n"))))))

(defun istari-next ()
  "Send next line to Istari."
  (interactive)
  (unless ist-running
    (istari-start))
  (if (eq (current-buffer) ist-source-buffer)
      (let* ((start (overlay-end ist-cursor))
             (end (next-line-position start)))
        (if (= start end) ; end of buffer
            (ding)
          (ist-send end)))
    (error "Istari running in another buffer.")))

(defun istari-goto (pos)
  "Send code to Istari or rewind Istari state."
  (interactive "d")
  (unless ist-running
    (istari-start))
  (if (eq (current-buffer) ist-source-buffer)
      (if (>= pos (overlay-end ist-cursor))
          (ist-send pos)
        (ist-rewind pos))
    (error "Istari running in another buffer.")))

(defun istari-prev ()
  "Rewind UI to previous line."
  (interactive)
  (unless ist-running
    (error "Istari not running."))
  (if (eq (current-buffer) ist-source-buffer)
      (ist-rewind (save-excursion
                    (goto-char (overlay-end ist-cursor))
                    (forward-line -1)
                    (point)))
    (error "Istari running in another buffer.")))

(defun istari-goto-marker ()
  "Move to Istari input marker."
  (interactive)
  (unless ist-running
    (error "Istari not running."))
  (if (not (eq (current-buffer) ist-source-buffer))
      (switch-to-buffer ist-source-buffer))
  (goto-char (overlay-start ist-cursor)))

(defun istari-interrupt ()
  "Interrupt Istari process."
  (interactive)
  (unless ist-running
    (error "Istari not running."))
  (interrupt-process ist-ml-proc)
  (sleep-for 0 10) ;; on some platforms, SML needs time to deal with an interrupt before we send more code
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

(defun istari-cycle-binaries ()
  "Cycle through Istari binaries."
  (interactive)
  (progn
    (setq istari-binary-index (1+ istari-binary-index))
    (let*
        ((l (reverse istari-binaries))
         (x (nth istari-binary-index l))
         (y (if x
                x
              (progn
                (setq istari-binary-index 0)
                (car l)))))
      (setq istari-binary (cdr y))
      (message (car y)))))


;; This is to make (thing-at-point 'longid) work

(defun skip-longid-forward (&optional arg)
  (if
      (and arg (< arg 0))
      (skip-syntax-backward "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ'_.")
  (skip-syntax-forward "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ'_.")))

(put 'longid 'forward-op 'skip-longid-forward)


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
  (interactive
   (list (read-from-minibuffer "Constant: " (thing-at-point 'longid))))
  (istari-interject (concat "Report.show (parseLongident /" str "/);")))
  
(defun istari-report-type (str)
  "Report the type of a constant."
  (interactive
   (list (read-from-minibuffer "Constant: " (thing-at-point 'longid))))
  (istari-interject (concat "Report.showType (parseLongident /" str "/);")))

(defun istari-report-search (str)
  "Report constants whose type mentions each target constant."
  (interactive "MConstants: ")
  (istari-interject (concat "Report.search (parseConstants /" str "/) [];")))

(defun istari-show-implicits ()
  "Toggle showing implicit arguments."
  (interactive)
  (istari-interject "Show.showImplicits := not (!Show.showImplicits); if !Show.showImplicits then print \"Display of implicit arguments enabled.\\n\" else print \"Display of implicit arguments disabled.\\n\";"))

(defun istari-show-substitutions ()
  "Toggle showing substitutions."
  (interactive)
  (istari-interject "Show.showSubstitutions := not (!Show.showSubstitutions); if !Show.showSubstitutions then print \"Display of evar substitutions enabled.\\n\" else print \"Display of evar substitutions disabled.\\n\";"))

(defun istari-insert-application (str)
  "Insert application for a constant."
  (interactive
   (list (read-from-minibuffer "Constant: " (thing-at-point 'longid))))
  (istari-interject (concat "Report.insertApp (parseLongident /" str "/);"))
  (setq ist-permit-insert t))

(defun istari-insert-intros ()
  "Insert intros for the current goal."
  (interactive)
  (istari-interject "Report.insertIntros ();")
  (setq ist-permit-insert t))

(run-hooks 'istari-hook)
