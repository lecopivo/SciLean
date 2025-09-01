;;; Directory Local Variables
;;; For more information see (info "(emacs) Directory Variables")

((lean4-mode . ((fill-column . 100)
                (show-trailing-whitespace . t)
                (eval . (add-hook 'before-save-hook 'delete-trailing-whitespace nil t)))))



;; hide warning/note/info from compilation output
;; ((nil . ((eval . (progn
;;                    (require 'compile)
;;                    (defun my-hide-compilation-warnings ()
;;                      "Hide lines in compilation buffer that start with 'warning:', 'note:', or 'info:'."
;;                      (save-excursion
;;                        (goto-char (point-min))
;;                        (while (re-search-forward "^\\(warning\\|note\\|info\\):.*\n" nil t) 
;;                          (replace-match ""))))
;;                    (defun my-add-compilation-hook ()
;;                      "Add compilation filter hook if buffer is visiting a file."
;;                      (when buffer-file-name
;;                        (add-hook 'compilation-filter-hook 'my-hide-compilation-warnings)))
;;                    (add-hook 'find-file-hook 'my-add-compilation-hook))))))
