;;; Directory Local Variables
;;; For more information see (info "(emacs) Directory Variables")

((lean4-mode . ((fill-column . 100)
                (show-trailing-whitespace . t)
                (eval . (add-hook 'before-save-hook 'delete-trailing-whitespace nil t)))))
