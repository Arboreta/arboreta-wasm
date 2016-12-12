(defpackage :borealis
 (:use "COMMON-LISP" "HUNCHENTOOT" "CL-WHO" "PARENSCRIPT" "CL-FAD")
) (in-package :borealis)

(setq site-instance (hunchentoot::make-instance 
		  'hunchentoot::easy-acceptor :port 8004))


(define-easy-handler (test-page :uri "/") ()
  (with-html-output-to-string (s)
    (:html
     (:head (:title "WebAssembly Test")
	    ;; future wasm js api will support <script> for wasm
	    ;; creates 'instance' object 
	    (:script :type "text/javascript" 
		     (str "
req = new XMLHttpRequest();
req.open('GET', 'output/out.wasm', true);
req.responseType = 'arraybuffer';

req.onload = function (oEvent) {
  buf = new Uint8Array(req.response);
}; req.send(null);
Wasm.instantiateModule(buf);"		  
		      ))
	    (:body :bgcolor "black" :style "color:#FFFFFF;"
		   (:div :id "container"))
	    ))))

(push (hunchentoot:create-folder-dispatcher-and-handler
       "/output/" (concatenate 'string (sb-posix:getcwd) "/output/")) hunchentoot:*dispatch-table*)

(defun main ()  
  (hunchentoot::start site-instance)
  (read))

(sb-ext:save-lisp-and-die "test" :toplevel #'main :executable t)


