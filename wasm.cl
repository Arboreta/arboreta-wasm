;;; -*- mode: Common-Lisp; Base: 10; Syntax: ANSI-Common-Lisp; tab-width: 8; indent-tabs-mode: nil -*-
;;;
;;; Copyright 2016 Douglas Crosher
;;;
;;; Licensed under the Apache License, Version 2.0 (the "License");
;;; you may not use this file except in compliance with the License.
;;; You may obtain a copy of the License at
;;;
;;;    http://www.apache.org/licenses/LICENSE-2.0
;;;
;;; Unless required by applicable law or agreed to in writing, software
;;; distributed under the License is distributed on an "AS IS" BASIS,
;;; WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
;;; See the License for the specific language governing permissions and
;;; limitations under the License.
;;;


;;;; Support.

(defun %double-float-bits (n)
  (declare (type double-float n))
  #+(and scl 64bit)
  (kernel:double-float-bits n)
  #+(or cmu (and scl (not 64bit)))
  (let ((high (kernel:double-float-high-bits n))
        (low (kernel:double-float-low-bits n)))
    (logior (ash high 32) low))
  #+sbcl
  (let ((high (sb-kernel:double-float-high-bits n))
        (low (sb-kernel:double-float-low-bits n)))
    (logior (ash high 32) low))
  #+ccl
  (multiple-value-bind (high low)
      (ccl::double-float-bits n)
    (logior (ash high 32) low))
  #+abcl
  (let ((high (system:double-float-high-bits n))
        (low (system:double-float-low-bits n)))
    (logior (ash high 32) low))
  #-(or scl cmu sbcl ccl abcl) (error "not supported")
  )

(defun %single-float-bits (n)
  (declare (type single-float n))
  #+(or scl cmu)
  (kernel:single-float-bits n)
  #+sbcl
  (sb-kernel:single-float-bits n)
  #+ccl
  (ccl::single-float-bits n)
  #+abcl
  (system:single-float-bits n)
  #-(or scl cmu sbcl ccl abcl) (error "not supported")
  )

(defun %make-double-float (bits)
  (declare (type (signed-byte 64) bits))
  #+(and scl 64bit)
  (kernel:make-double-float bits)
  #+(or cmu (and scl (not 64bit)))
  (kernel:make-double-float (ash bits -32) (ldb (byte 32 0) bits))
  #+sbcl
  (sb-kernel:make-double-float (ash bits -32) (ldb (byte 32 0) bits))
  #+ccl
  (ccl::double-float-from-bits (ldb (byte 32 32) bits) (ldb (byte 32 0) bits))
  #+abcl
  (system:make-double-float bits)
  #-(or scl cmu sbcl ccl abcl) (error "not supported")
  )

(defun %make-single-float (bits)
  (declare (type (signed-byte 32) bits))
  #+(or cmu scl)
  (kernel:make-single-float bits)
  #+sbcl
  (sb-kernel:make-single-float bits)
  #+ccl
  (ccl::host-single-float-from-unsigned-byte-32 (logand bits #xffffffff))
  #+abcl
  (system::make-single-float n)
  #-(or scl cmu sbcl ccl abcl) (error "not supported")
  )


;;;; The wasm binary format.

(defparameter *wasm-page-size* #x10000) ; 64k

;;; Mapping operator names to their opcodes and argument and results types.
;;;
;;; The types used are:
;;;  i32 - single value 32 bit integer type.
;;;  i64 - single value 64 bit integer type.
;;;  f32 - single value 32 bit float type.
;;;  f64 - single value 64 bit float type.
;;;  ()  - zero values type, e.g. result of 'nop, and 'br_if.
;;;  e   - empty type. e.g. result type of 'br and 'unreachable. Top-down
;;;        type checking succeeds for any operator returning the empty type
;;;        irrespective of the expected type. Bottom up checking passes the
;;;        empty type up through operators such as 'if_else and succeeds for
;;;        any expected type.
;;;  p   - 'parametric' type. Any type including multi-values types, but all
;;;        instances must be consistent. The empty-type is also passed through
;;;        parametric operands.
;;;  *   - zero or multiple values of any type. Perhaps also the empty-type?
;;;  u8-imm - an immediate unsigned 8 bit integer.
;;;  i32-imm - an immediate 32 bit integer, leb128 signed encoded.
;;;  i64-imm - an immediate 64 bit integer, leb128 signed encoded.
;;;  f32-imm - an immediate 32 bit float.
;;;  f64-imm - an immediate 64 bit float.
;;;  (mem <n>) - memory access optional arguments, an offset and alignment. The
;;;              offset defaults to zero, and the operators natural alignment is
;;;              given by 'n. The actual address would typically follow in a
;;;              separate argument, but is split out here to allow the address
;;;              to be computed from a number of other arguments.
;;;  branch - a branch label
;;;  i32-local - an i32 variable index
;;;  i64-local - an i64 variable index
;;;  f32-local - a f32 variable index
;;;  f64-local - a f64 variable index
;;;  local - a local variable label, where the index is constrained to match the
;;;          operator result expected type.
;;;  global - a global variable label, v8 specific and might be the thread local
;;;           variables someday.
;;;  sig - an immediate function signature index.
;;;
;;; The operator arguments are defined as:
;;;  1. A list of fixed argument types.
;;;  2. An optional type for a variable number of other arguments.
;;;
;;; An operator with only fixed arguments need not encode the number of
;;; arguments. Operators with a variable number of arguments encode the number
;;; of optional arguments, not counting any fixed arguments. Hopefully the
;;; number of arguments can be encoded in a consistent position even with some
;;; fixed arguments so that the position of this length need not be also
;;; declared.
;;;
;;; Possible extensions:
;;; * A list of optional argument types immediately following the fixed
;;;   arguments.
;;; * A list of optional argument types following the single-type optional
;;;   arguments, allowing the trailing arguments to have different types.
;;; * Extend to multiple values types which would be (type1 type2 ... typen).
;;;
;;; This table is not adequate to define all the operators, and special cases
;;; are noted. For the encoder and decoder the special cases are only the
;;; functions calls, 'block, 'loop, 'tableswitch and 'return - all the other
;;; operators have table driven encoding and decoding.
;;;
;;; ml check_type passes if expected is None or types are equal.
;;; seems consistent with the caller ignoring unused values.
(defparameter *wasm-opcodes*
  '(;; Name, code, fixed arg types, rest arg type, result types.
    ;; check_type None et e.at
    (nop                 #x00  () nil                  ())
    ;; Special case encoder, decoder and validator: there is an optional label
    ;; that needs binding when processing the sub expressions. A block must have
    ;; at least one expression. Only the last expression is parametric with the
    ;; result, the rest of the expresions expect the type '().
    (block               #x01  () p                     p)
    ;; Special case encoder, decoder, and validator: labels, their binding,
    ;; result type.
    (loop                #x02  () p                     p)
    ;;
    (if                  #x03  (i32 nil) nil           ())
    ;; Special case validator: the results of the two paths are parametric with
    ;; the result but need not be the same type. For example one might be the
    ;; empty type and the other a f64 when the result is f64 or '().
    (if_else             #x04  (i32 p p) nil            p) ; if_then.
    ;;
    ;; Special case validator: parametric.
    (select              #x05  (p p i32) nil            p)
    ;;
    ;; Special cases validator: the value is optional in the wast. The v8
    ;; encoding fills the value with a 'nop when not supplied, but this does not
    ;; validate under the ml-prot.
    ;; Resolution required here.
    (br                  #x06  (branch *) nil           e)
    (br_if               #x07  (branch * i32) nil      ())
    ;;
    ;; Special case encoder, decoder, and validator. Labels, and their binding.
    (br_table            #x08  () *                     e)
    ;;
    ;; Special case encoder, decoder, validator: optional value in wast.
    ;; Resolution required here: v8 looks at the function signature to determine
    ;; the arity of the return, which fails for a 'nop result.
    (return              #x14  (*) nil                  e)
    (unreachable         #x15  () nil                   e)
    ;;
    (i32.const           #x0a  (i32-imm) nil          i32)
    (i64.const           #x0b  (i64-imm) nil          i64)
    (f64.const           #x0c  (f64-imm) nil          f64)
    (f32.const           #x0d  (f32-imm) nil          f32)
    ;; Special case: result type depends on the variable type.
    (get_local           #x0e  (local) nil              p)
    (i32.get_local       #x0e  (i32-local) nil        i32)
    (i64.get_local       #x0e  (i64-local) nil        i64)
    (f32.get_local       #x0e  (f32-local) nil        f32)
    (f64.get_local       #x0e  (f64-local) nil        f64)
    ;; Special case: result type depends on the variable type.
    (set_local           #x0f  (local p) nil            p)
    (i32.set_local       #x0f  (i32-local p) nil      i32)
    (i64.set_local       #x0f  (i64-local p) nil      i64)
    (f32.get_local       #x0f  (f32-local p) nil      f32)
    (f64.set_local       #x0f  (f64-local p) nil      f64)
    ;;
    ;; Special cases for the encoder, decoder, and validation: fixed args, but
    ;; from the signature.
    (call                #x12  (fn) *                   *)
    (call_indirect       #x13  (sig i32) *              *)
    (call_import         #x1f  (fn) *                   *)
    ;;
    (i32.load8_s         #x20  ((mem 1) i32) nil      i32)
    (i32.load8_u         #x21  ((mem 1) i32) nil      i32)
    (i32.load16_s        #x22  ((mem 2) i32) nil      i32)
    (i32.load16_u        #x23  ((mem 2) i32) nil      i32)
    (i64.load8_s         #x24  ((mem 1) i32) nil      i64)
    (i64.load8_u         #x25  ((mem 1) i32) nil      i64)
    (i64.load16_s        #x26  ((mem 2) i32) nil      i64)
    (i64.load16_u        #x27  ((mem 2) i32) nil      i64)
    (i64.load32_s        #x28  ((mem 4) i32) nil      i64)
    (i64.load32_u        #x29  ((mem 4) i32) nil      i64)
    (i32.load            #x2a  ((mem 4) i32) nil      i32)
    (i64.load            #x2b  ((mem 8) i32) nil      i64)
    (f32.load            #x2c  ((mem 4) i32) nil      f32)
    (f64.load            #x2d  ((mem 8) i32) nil      f64)
    (i32.store8          #x2e  ((mem 1) i32 i32) nil  i32)
    (i32.store16         #x2f  ((mem 2) i32 i32) nil  i32)
    (i64.store8          #x30  ((mem 1) i32 i64) nil  i64)
    (i64.store16         #x31  ((mem 2) i32 i64) nil  i64)
    (i64.store32         #x32  ((mem 4) i32 i64) nil  i64)
    (i32.store           #x33  ((mem 4) i32 i32) nil  i32)
    (i64.store           #x34  ((mem 8) i32 i64) nil  i64)
    (f32.store           #x35  ((mem 4) i32 f32) nil  f32)
    (f64.store           #x36  ((mem 8) i32 f64) nil  f64)
    (memory_size         #x3b  () nil                 i32)
    (grow_memory         #x39  (i32) nil              i32) ; resize_mem_l
    (resize_mem_h        #x3a  (i32) nil              i32) ; ??
    (i32.add             #x40  (i32 i32) nil          i32)
    (i32.sub             #x41  (i32 i32) nil          i32)
    (i32.mul             #x42  (i32 i32) nil          i32)
    (i32.div_s           #x43  (i32 i32) nil          i32)
    (i32.div_u           #x44  (i32 i32) nil          i32)
    (i32.rem_s           #x45  (i32 i32) nil          i32)
    (i32.rem_u           #x46  (i32 i32) nil          i32)
    (i32.and             #x47  (i32 i32) nil          i32)
    (i32.or              #x48  (i32 i32) nil          i32)
    (i32.xor             #x49  (i32 i32) nil          i32)
    (i32.shl             #x4a  (i32 i32) nil          i32)
    (i32.shr_u           #x4b  (i32 i32) nil          i32)
    (i32.shr_s           #x4c  (i32 i32) nil          i32)
    (i32.rotr            #xb6  (i32 i32) nil          i32)
    (i32.rotl            #xb7  (i32 i32) nil          i32)
    (i32.eq              #x4d  (i32 i32) nil          i32)
    (i32.ne              #x4e  (i32 i32) nil          i32)
    (i32.lt_s            #x4f  (i32 i32) nil          i32)
    (i32.le_s            #x50  (i32 i32) nil          i32)
    (i32.lt_u            #x51  (i32 i32) nil          i32)
    (i32.le_u            #x52  (i32 i32) nil          i32)
    (i32.gt_s            #x53  (i32 i32) nil          i32)
    (i32.ge_s            #x54  (i32 i32) nil          i32)
    (i32.gt_u            #x55  (i32 i32) nil          i32)
    (i32.ge_u            #x56  (i32 i32) nil          i32)
    (i32.clz             #x57  (i32) nil              i32)
    (i32.ctz             #x58  (i32) nil              i32)
    (i32.popcnt          #x59  (i32) nil              i32)
    (i32.eqz             #x5a  (i32) nil              i32)
    (i64.add             #x5b  (i64 i64) nil          i64)
    (i64.sub             #x5c  (i64 i64) nil          i64)
    (i64.mul             #x5d  (i64 i64) nil          i64)
    (i64.div_s           #x5e  (i64 i64) nil          i64)
    (i64.div_u           #x5f  (i64 i64) nil          i64)
    (i64.rem_s           #x60  (i64 i64) nil          i64)
    (i64.rem_u           #x61  (i64 i64) nil          i64)
    (i64.and             #x62  (i64 i64) nil          i64)
    (i64.or              #x63  (i64 i64) nil          i64)
    (i64.xor             #x64  (i64 i64) nil          i64)
    (i64.shl             #x65  (i64 i64) nil          i64)
    (i64.shr_u           #x66  (i64 i64) nil          i64)
    (i64.shr_s           #x67  (i64 i64) nil          i64)
    (i64.rotr            #xb8  (i64 i64) nil          i64)
    (i64.rotl            #xb9  (i64 i64) nil          i64)
    (i64.eq              #x68  (i64 i64) nil          i32)
    (i64.ne              #x69  (i64 i64) nil          i32)
    (i64.lt_s            #x6a  (i64 i64) nil          i32)
    (i64.le_s            #x6b  (i64 i64) nil          i32)
    (i64.lt_u            #x6c  (i64 i64) nil          i32)
    (i64.le_u            #x6d  (i64 i64) nil          i32)
    (i64.gt_s            #x6e  (i64 i64) nil          i32)
    (i64.ge_s            #x6f  (i64 i64) nil          i32)
    (i64.gt_u            #x70  (i64 i64) nil          i32)
    (i64.ge_u            #x71  (i64 i64) nil          i32)
    (i64.clz             #x72  (i64) nil              i64)
    (i64.ctz             #x73  (i64) nil              i64)
    (i64.popcnt          #x74  (i64) nil              i64)
    (i64.eqz             #xba  (i64) nil              i64)
    (f32.add             #x75  (f32 f32) nil          f32)
    (f32.sub             #x76  (f32 f32) nil          f32)
    (f32.mul             #x77  (f32 f32) nil          f32)
    (f32.div             #x78  (f32 f32) nil          f32)
    (f32.min             #x79  (f32 f32) nil          f32)
    (f32.max             #x7a  (f32 f32) nil          f32)
    (f32.abs             #x7b  (f32) nil              f32)
    (f32.neg             #x7c  (f32) nil              f32)
    (f32.copysign        #x7d  (f32 f32) nil          f32)
    (f32.ceil            #x7e  (f32) nil              f32)
    (f32.floor           #x7f  (f32) nil              f32)
    (f32.trunc           #x80  (f32) nil              f32)
    (f32.nearest         #x81  (f32) nil              f32)
    (f32.sqrt            #x82  (f32) nil              f32)
    (f32.eq              #x83  (f32 f32) nil          i32)
    (f32.ne              #x84  (f32 f32) nil          i32)
    (f32.lt              #x85  (f32 f32) nil          i32)
    (f32.le              #x86  (f32 f32) nil          i32)
    (f32.gt              #x87  (f32 f32) nil          i32)
    (f32.ge              #x88  (f32 f32) nil          i32)
    (f64.add             #x89  (f64 f64) nil          f64)
    (f64.sub             #x8a  (f64 f64) nil          f64)
    (f64.mul             #x8b  (f64 f64) nil          f64)
    (f64.div             #x8c  (f64 f64) nil          f64)
    (f64.min             #x8d  (f64 f64) nil          f64)
    (f64.max             #x8e  (f64 f64) nil          f64)
    (f64.abs             #x8f  (f64) nil              f64)
    (f64.neg             #x90  (f64) nil              f64)
    (f64.copysign        #x91  (f64 f64) nil          f64)
    (f64.ceil            #x92  (f64) nil              f64)
    (f64.floor           #x93  (f64) nil              f64)
    (f64.trunc           #x94  (f64) nil              f64)
    (f64.nearest         #x95  (f64) nil              f64)
    (f64.sqrt            #x96  (f64) nil              f64)
    (f64.eq              #x97  (f64 f64) nil          i32)
    (f64.ne              #x98  (f64 f64) nil          i32)
    (f64.lt              #x99  (f64 f64) nil          i32)
    (f64.le              #x9a  (f64 f64) nil          i32)
    (f64.gt              #x9b  (f64 f64) nil          i32)
    (f64.ge              #x9c  (f64 f64) nil          i32)
    (i32.trunc_s/f32     #x9d  (f32) nil              i32) ; i32.sconvert_f32
    (i32.trunc_s/f64     #x9e  (f64) nil              i32) ; i32.sconvert_f64
    (i32.trunc_u/f32     #x9f  (f32) nil              i32) ; i32.uconvert_f32
    (i32.trunc_u/f64     #xa0  (f64) nil              i32) ; i32.uconvert_f64
    (i32.wrap/i64        #xa1  (i64) nil              i32) ; i32.convert.i64
    (i64.trunc_s/f32     #xa2  (f32) nil              i64) ; i64.sconvert_f32
    (i64.trunc_s/f64     #xa3  (f64) nil              i64) ; i64.sconvert_f64
    (i64.trunc_u/f32     #xa4  (f32) nil              i64) ; i64.uconvert_f32
    (i64.trunc_u/f64     #xa5  (f64) nil              i64) ; i64.uconvert_f64
    (i64.extend_s/i32    #xa6  (i32) nil              i64) ; i64.sconvert_i32
    (i64.extend_u/i32    #xa7  (i32) nil              i64) ; i64.uconvert_i32
    (f32.convert_s/i32   #xa8  (i32) nil              f32) ; f32.sconvert_i32
    (f32.convert_u/i32   #xa9  (i32) nil              f32) ; f32.uconvert_i32
    (f32.convert_s/i64   #xaa  (i64) nil              f32) ; f32.sconvert_i64
    (f32.convert_u/i64   #xab  (i64) nil              f32) ; f32.uconvert_i64
    (f32.demote/f64      #xac  (f64) nil              f32) ; f32.convert_f64
    (f32.reinterpret/i32 #xad  (i32) nil              f32) ; f32.reinterpret_i32
    (f64.convert_s/i32   #xae  (i32) nil              f64) ; f64.sconvert_i32
    (f64.convert_u/i32   #xaf  (i32) nil              f64) ; f64.uconvert_i32
    (f64.convert_s/i64   #xb0  (i64) nil              f64) ; f64.sconvert_i64
    (f64.convert_u/i64   #xb1  (i64) nil              f64) ; f64.uconvert_i64
    (f64.promote/f32     #xb2  (f32) nil              f64) ; f64.convert_f32
    (f64.reinterpret/i64 #xb3  (i64) nil              f64) ; f64.reinterpret_i64
    (i32.reinterpret/f32 #xb4  (f32) nil              i32) ; i32.reinterpret_f32
    (i64.reinterpret/f64 #xb5  (f64) nil              i64) ; i64.reinterpret_f64
    ))



;;;; Importing wast.

(defparameter *wast-readtable*
  (let ((table (copy-readtable)))
    (setf (readtable-case table)
          #+scl (if (eq ext:*case-mode* :lower) :preserve :invert)
          #-scl :invert)
    table)
  "A custom readtable for wast files which uses lowercase by default and
  preserves case. For standard CL implementations invert the case, and for
  non-standard lowercase implementations preserve the case.")

;;; Support presentation as raw bits or a number.
(defparameter *wast-float-style* :number)

(defun parse-hex-float (string start end format)
  "Parse a hex-float, returning a floating point number. The 0x prefix
  is assumed to have already been read."
  (declare (type simple-string string)
           (fixnum start end)
           (type (member double-float single-float) format))
  (let ((number 0)
        (numberp nil)
	(divisor 1)
	(negative-exponent nil)
	(exponent 0)
	(char (schar string start)))
    (flet ((read-buffer ()
             (incf start)
             (if (< start end)
                 (schar string start)
                 #\null)))
      ;; Read digits before the dot.
      (do* ((ch char (read-buffer))
            (dig (digit-char-p ch 16) (digit-char-p ch 16)))
           ((not dig) (setq char ch))
        (setf numberp t)
        (setq number (+ (* number 16) dig)))
      ;; Deal with the dot, if it's there.
      (when (char= char #\.)
        (setq char (read-buffer))
        ;; Read digits after the dot.
        (do* ((ch char (read-buffer))
              (dig (and (char/= ch #\null) (digit-char-p ch 16))
                   (and (char/= ch #\null) (digit-char-p ch 16))))
             ((not dig) (setq char ch))
          (setq divisor (* divisor 16))
          (setq number (+ (* number 16) dig))))
      ;; Is there an exponent letter?
      (unless (or numberp (> divisor 1))
        (error "Unexpected hex-float, no significant digits"))
      (unless (member char '(#\p #\P))
        (error "Unexpected hex-float, no exponent"))
      ;; Build exponent.
      (setq char (read-buffer))
      ;; Check leading sign.
      (if (cond ((char= char #\+) t)
                ((char= char #\-) (setq negative-exponent t)))
          ;; Flush sign.
          (setq char (read-buffer)))
      ;; Read digits for exponent.
      (do* ((ch char (read-buffer))
            (dig (and (char/= ch #\null) (digit-char-p ch))
                 (and (char/= ch #\null) (digit-char-p ch))))
           ((not dig)
            (setq exponent (if negative-exponent (- exponent) exponent)))
        (setq exponent (+ (* exponent 2) dig)))
      ;; Generate and return the float, depending on FLOAT-CHAR:
      (coerce (/ (* (expt 2 exponent) number) divisor) format))))


(defun parse-wast-float (string &key (start 0) (end (length string))
                                  (format 'double-float))
  "Parse a wast literal float in the 'format specified."
  (let ((negp nil)
        (c (schar string start)))
    (cond ((char= c #\-)
           (setf negp t)
           (incf start))
          ((char= c #\+)
           (incf start)))
    (let ((pos (cond ((string= string "infinity" :start1 start :end1 end)
                      (ecase format
                        (double-float #x7FF0000000000000)
                        (single-float #x7F800000)))
                     ((string= string "nan" :start1 start :end1 end)
                      (ecase format
                        (double-float #x7ff8000000000000)
                        (single-float #x7fc00000)))
                     ((string= string "nan:" :start1 start :end1 (+ start 4))
                      (incf start 4)
                      (assert (and (char= (schar string start) #\0)
                                   (char= (schar string (1+ start)) #\x)))
                      (incf start 2)
                      (let ((n (parse-integer string :start start :end end :radix 16)))
                        (ecase format
                          (double-float (logior #x7ff0000000000000 n))
                          (single-float (logior #x7f800000 n)))))
                     ((string= string "0x" :start1 start :end1 (+ start 2))
                      (incf start 2)
                      (let ((n (parse-hex-float string start end format)))
                        (ecase format
                          (double-float (%double-float-bits n))
                          (single-float (%single-float-bits n)))))
                     (t
                      (let* ((*read-default-float-format* format)
                             (*read-eval* nil)
                             (n (read-from-string string t nil :start start :end end)))
                        (when (integerp n)
                          (setf n (coerce n format)))
                        (ecase format
                          (double-float (%double-float-bits n))
                          (single-float (%single-float-bits n))))))))
      (cond (negp
             (ecase format
               (double-float
                (assert (not (logbitp 63 pos)))
                (- pos #x8000000000000000))
               (single-float
                (assert (not (logbitp 31 pos)))
                (- pos #x80000000))))
            (t
             pos)))))


(defun map-wasm-functions (function ast)
  "Map over the functions in the 'ast module, call 'function with the:
  name, arguments, result types, local variables, and the body."
  (dolist (fn ast)
    (when (and (consp fn) (eq (first fn) 'func))
      (let ((name (second fn))
            (args (third fn))
            (results (fourth fn))
            (body (cddddr fn))
            (locals nil))
        ;; Local variables definitions.
        (when (eq (caar body) 'let)
          (assert (endp (cdr body)))
          (setf locals (cadar body))
          (setf body (cddar body)))
        (funcall function name args results locals body)))))


;;; The wast function operand declarations and local variable declarations
;;; are laborious to work with.  This reversible transform factors out some of
;;; the work involved in dealing these patterns by grouping them in fixed
;;; positions.
;;;
;;; They are not grouped in the function definition and might not even be
;;; present. This demands walking the list every time to get basic information.
;;; For example:
;;; (func $fn (param $i1 i32) (param $i2 i32) (param $i3 i32) (result i32) ...)
;;; (func $fn (param $i1 i32) ...)
;;; (func $fn (result i32) ...)
;;;
;;; In the function type signature declarations and the import types the operand
;;; types are group by 'param and 'result but either many be empty or
;;; missing. They are grouped into fixed positions and the 'param and 'result
;;; symbols dropped as the are no longer necessary.
;;;
;;; The wast also allows params to omit the label and allows a 'local
;;; declaration to be either a name-type pair or a list of unlabeled types. The
;;; locals are given a label here and references updated to use the label.
;;;
;;; The wast allows function names to be omitted, and they are given a label
;;; here, and references in calls and exports updated to use these labels.
;;;
;;; The function local variable declarations are listed after the operand and
;;; not grouped or in a fixed position. They are grouped into a fixed position
;;; in the function definition.
;;;
;;; The wast makes block labels and loop labels option and allows numeric depth
;;; references. Labels are added to all locations giving blocks and loops a
;;; fixed structure, and unused labels are set to 'nil.
;;;
;;; Functions can reference their type using a signature label or index, these
;;; are converted into function declarations.
;;;
;;; The indexed targets in a br_table are grouped into a list to give
;;; the other arguments a fixed position.
;;;
;;; The exporting of memory is rewritten to keep it separate from
;;; exporting functions.
;;;
;;; The 'if operator has implicit blocks and then/else blocks.
;;;
(defun import-wast-func-decl (wast)
  "Import the wast style function declarations grouping the arguments, results,
  and local variable declarations in a fixed pattern. The function type
  declarations for the signatures and imports are also grouped. The 'wast is
  destructively modified."
  (let ((function-names nil)
        (import-names nil)
        (signatures nil))
    (flet ((rewrite-func-decl (decl)
             (let ((params nil)
                   (results nil))
               (loop
                  (let ((next (pop decl)))
                    (unless next
                      (return))
                    (ecase (first next)
                      (param
                       (setf params (append params (rest next))))
                      (result
                       (setf results (append results (rest next)))))))
               (list params results))))
      ;; First pass to get the types.
      (dolist (form (rest wast))
        (cond ((not (consp form)))
              ((eq (first form) 'type)
               (let ((decl (rest form))
                     (name nil))
                 (when (symbolp (first decl))
                   (setf name (pop decl)))
                 (setf decl (first decl))
                 (when (eq (first decl) 'func)
                   (let ((fn-decl (rewrite-func-decl (rest decl))))
                     (setf (rest decl) fn-decl)
                     (push (cons name fn-decl) signatures)))))))
      (setf signatures (nreverse signatures))
      ;;
      (dolist (form (rest wast))
        (cond ((not (consp form)))
              ((eq (first form) 'func)
               (let ((name nil)
                     (type-signature nil)
                     (params nil)
                     (results nil)
                     (locals nil)
                     (el (rest form))
                     ;;
                     ;; Local and param names.
                     (all-locals nil)
                     (i32-locals-count 0)
                     (i64-locals-count 0)
                     (f32-locals-count 0)
                     (f64-locals-count 0))
                 (flet ((note-local (name type)
                          (assert (not (member name all-locals)))
                          (push name all-locals)
                          (ecase type
                            (i32 (incf i32-locals-count))
                            (i64 (incf i64-locals-count))
                            (f32 (incf f32-locals-count))
                            (f64 (incf f64-locals-count))))
                        (make-local-name (type)
                          (let ((name (intern (ecase type
                                                (i32 (format nil "~A~d" '#:$i i32-locals-count))
                                                (i64 (format nil "~A~d" '#:$j i64-locals-count))
                                                (f32 (format nil "~A~d" '#:$f f32-locals-count))
                                                (f64 (format nil "~A~d" '#:$d f64-locals-count))))))
                            (assert (not (member name all-locals)))
                            name))
                        )
                   ;; Name is optional.
                   (when (and el (symbolp (first el)))
                     (setf name (pop el)))
                   ;; Name the function if not already named.
                   (unless name
                     (setf name (intern (format nil "~A~D" '#:$f (length function-names)) :cl-user)))
                   (push name function-names)
                   ;; Check for a type, but just note it now.
                   (when (consp el)
                     (let ((type (first el)))
                       (when (and (consp type) (eq (first type) 'type))
                         (setf type-signature (pop el)))))
                   ;; Params and results.
                   (loop
                      (let ((next (pop el)))
                        (unless next
                          (return))
                        (let ((len (length next)))
                          (cond ((eq (first next) 'param)
                                 ;; Might be a list of types.
                                 (cond ((dolist (type (rest next) t)
                                          (unless (member type '(i32 i64 f32 f64))
                                            (return nil)))
                                        (dolist (type (rest next))
                                          (let ((name (make-local-name type)))
                                            (note-local name type)
                                            (push (list name type) params))))
                                       (t
                                        (assert (= len 3))
                                        (let ((name (second next))
                                              (type (third next)))
                                          (note-local name type)
                                          (push (rest next) params)))))
                                ((eq (first next) 'result)
                                 (assert (= len 2))
                                 (push (second next) results))
                                (t
                                 (push next el)
                                 (return))))))
                   ;;
                   (when type-signature
                     (let ((type-params nil)
                           (type-results nil))
                       (let* ((name (second type-signature))
                              (decl (cond ((integerp name)
                                           (cdr (elt signatures name)))
                                          ((symbolp name)
                                           (cdr (assoc name signatures)))
                                          (t
                                           (error "Unexpected signature name: ~S~%" name)))))
                         (setf type-params (first decl))
                         (setf type-results (second decl))
                         (cond ((or params results)
                                ;; Check they have the same types.
                                (assert (= (length params) (length type-params)))
                                (do ((params params (rest params))
                                     (type-params type-params (rest type-params)))
                                    ((endp params))
                                  (assert (eq (first type-params) (second (first params)))))
                                (assert (equalp type-results results)))
                               (t
                                ;; Use the type to create the params and results.
                                (dolist (type type-params)
                                  (let ((name (make-local-name type)))
                                    (note-local name type)
                                    (push (list name type) params)))
                                (dolist (result type-results)
                                  (push result results)))))))
                   ;;
                   ;; Now the locals if any.
                   (loop
                      (let ((next (pop el)))
                        (unless next
                          (return))
                        (let ((len (length next)))
                          (cond ((eq (first next) 'local)
                                 ;; Might be a list of types.
                                 (cond ((dolist (type (rest next) t)
                                          (unless (member type '(i32 i64 f32 f64))
                                            (return nil)))
                                        (dolist (type (rest next))
                                          (let ((name (make-local-name type)))
                                            (note-local name type)
                                            (push (list name type) locals))))
                                       (t
                                        (assert (= len 3))
                                        (let ((name (second next))
                                              (type (third next)))
                                          (note-local name type)
                                          (push (rest next) locals)))))
                                (t
                                 (push next el)
                                 (return))))))
                   (setf all-locals (nreverse all-locals))
                   ;; Replace any numeric local variable references with their label.
                   (labels ((relabel-local-refs (form)
                              (when (consp form)
                                (when (member (first form) '(get_local set_local))
                                  (let ((label (second form)))
                                    (when (integerp label)
                                      (setf (second form) (elt all-locals label)))))
                                (dolist (el form)
                                  (relabel-local-refs el)))))
                     (relabel-local-refs el))
                   (setf (car form) 'func)
                   (setf (cdr form) `(,name ,(nreverse params) ,(nreverse results)
                                            ,@(if locals
                                                  `((let ,(nreverse locals) ,@el))
                                                  el))))))
              ((eq (first form) 'import)
               (let* ((args (rest form))
                      (label (first args)))
                 ;; The label name is optional.
                 (cond ((symbolp label)
                        (pop args))
                       ((stringp label)
                        (setf label (intern (format nil "~A~D" '#:$fi (length import-names)) :cl-user))
                        (push label (rest form)))
                       (t
                        (error "Unexpected import form: ~S~%" form)))
                 (push label import-names)
                 (assert (stringp (pop args)))
                 (let ((last args))
                   (assert (stringp (pop args)))
                   (cond ((and (consp args)
                               (let ((type (first args)))
                                 (and (consp type) (eq (first type) 'type))))
                          (let* ((type (pop args))
                                 (name (second type))
                                 (decl (cond ((integerp name)
                                              (cdr (elt signatures name)))
                                             ((symbolp name)
                                              (cdr (assoc name signatures)))
                                             (t
                                              (error "Unexpected signature name: ~S~%" name)))))
                            (setf (rest last) decl)))
                         (t
                          (setf (rest last) (rewrite-func-decl (cddddr form))))))))
              ((eq (first form) 'export)
               (cond ((and (= (length form) 3)
                           (eq (third form) 'memory))
                      (setf (cddr form) nil)
                      (push 'memory (rest form)))
                     (t
                      (push 'func (rest form)))))
              ))
      ;;
      ;;
      ;; Convert numeric references to functions to a label.
      (setf function-names (nreverse function-names))
      (setf import-names (nreverse import-names))
      (dolist (form (rest wast))
        (cond ((not (consp form)))
              ((eq (first form) 'export)
               ;; Convert a number function index into a label here too.
               (let ((label (fourth form)))
                 (when (integerp label)
                   (setf (fourth form) (elt function-names label)))))
              ((eq (first form) 'table)
               (do ((labels (rest form) (rest labels)))
                   ((endp labels))
                 (let ((label (first labels)))
                   (when (integerp label)
                     (setf (first labels) (elt function-names label))))))
              ((eq (first form) 'start)
               (let ((label (second form)))
                 (when (integerp label)
                   (setf (second form) (elt function-names label)))))
              ))
      ;;
      ;; Convert numeric references in calls to a label, and add block labels
      ;; everwhere and relabel their references to be labels.
      (let ((label-count 0)
            (block-targets nil))
        (flet ((walk (name args results locals body)
                 (declare (ignore name args results locals))
                 (labels ((make-label ()
                            (let ((label (intern (format nil "~a~d" '#:$l label-count) :cl-user)))
                              (assert (not (member label block-targets)))
                              (incf label-count)
                              label))
                          (relabel (ast)
                            (when (consp ast)
                              (case (first ast)
                                (call
                                 (let ((label (second ast)))
                                   (when (integerp label)
                                     (setf (second ast) (elt function-names label))))
                                 (dolist (el (rest ast))
                                   (relabel el)))
                                (call_import
                                 (let ((label (second ast)))
                                   (when (integerp label)
                                     (setf (second ast) (elt import-names label))))
                                 (dolist (el (rest ast))
                                   (relabel el)))
                                (block
                                  (cond ((and (rest ast) (symbolp (second ast)))
                                         (let ((label (second ast)))
                                           (assert label)
                                           (push (cons label 0) block-targets)))
                                        (t
                                         (let ((label (make-label)))
                                           (push label (rest ast))
                                           (push (cons label 0) block-targets))))
                                  (dolist (el (cddr ast))
                                    (relabel el))
                                  (when (zerop (cdr (pop block-targets)))
                                    ;; Unused label, set to nil to note.
                                    (setf (second ast) nil)))
                                (loop
                                  (assert (rest ast)) ; Must be at least one expression.
                                  (cond ((and (symbolp (second ast)) (symbolp (third ast)))
                                         (push (cons (second ast) 0) block-targets)
                                         (push (cons (third ast) 0) block-targets))
                                        ((symbolp (second ast))
                                         ;; If there is only one label then it
                                         ;; is the repeat label, so fill a break
                                         ;; label first.
                                         (let ((label (make-label)))
                                           (push label (rest ast))
                                           (push (cons label 0) block-targets))
                                         (push (cons (third ast) 0) block-targets))
                                        (t
                                         (let ((label1 (make-label))
                                               (label2 (make-label)))
                                           (push label2 (rest ast))
                                           (push label1 (rest ast))
                                           (push (cons label1 0) block-targets)
                                           (push (cons label2 0) block-targets))))
                                  (dolist (el (cddr ast))
                                    (relabel el))
                                  (when (zerop (cdr (pop block-targets)))
                                    (setf (third ast) nil))
                                  (when (zerop (cdr (pop block-targets)))
                                    (setf (second ast) nil)))
                                (if
                                 (relabel (second ast))
                                 (ecase (length ast)
                                   (3
                                    (let ((then (third ast)))
                                      (setf then (cond ((eq (first then) 'then)
                                                        `(block ,@(rest then)))
                                                       (t
                                                        `(block ,then))))
                                      (setf (third ast) then)
                                      (relabel then)))
                                   (4
                                    (let ((then (third ast))
                                          (else (fourth ast)))
                                      (setf then (cond ((eq (first then) 'then)
                                                        `(block ,@(rest then)))
                                                       (t
                                                        `(block ,then))))
                                      (setf (third ast) then)
                                      (relabel then)
                                      (setf else (cond ((eq (first else) 'else)
                                                        `(block ,@(rest else)))
                                                       (t
                                                        `(block ,else))))
                                      (setf (fourth ast) else)
                                      (relabel else)
                                      (setf (first ast) 'if_else)))))
                                (tableswitch
                                  (assert (rest ast))
                                  (cond ((symbolp (second ast))
                                         (push (cons (second ast) 0) block-targets))
                                        (t
                                         (let ((label (make-label)))
                                           (push label (rest ast))
                                           (push (cons label 0) block-targets))))
                                  (dolist (el (cddr ast))
                                    (relabel el))
                                  (when (zerop (cdr (pop block-targets)))
                                    (setf (second ast) nil)))
                                (br_table
                                 (let ((target-table nil)
                                       (default-target nil)
                                       (expressions nil)
                                       (elements (rest ast)))
                                   (do ()
                                       ((endp elements))
                                     (let ((label (first elements)))
                                       (cond ((integerp label)
                                              (let ((use (elt block-targets label)))
                                                (incf (cdr use))
                                                (push (car use) target-table)))
                                             ((symbolp label)
                                              (let ((use (assoc label block-targets)))
                                                (incf (cdr use)))
                                              (push label target-table))
                                             (t
                                              (return))))
                                     (pop elements))
                                   ;; Default is the last label.
                                   (setf default-target (pop target-table))
                                   (setf target-table (nreverse target-table))
                                   (dolist (exp elements)
                                     (assert (consp exp))
                                     (relabel exp)
                                     (push exp expressions))
                                   (setf (rest ast) `(,target-table ,default-target ,@expressions))))
                                (br
                                 (let ((label (second ast)))
                                   (cond ((integerp label)
                                          (let ((use (elt block-targets label)))
                                            (incf (cdr use))
                                            (setf (second ast) (car use))))
                                         (t
                                          (let ((use (assoc label block-targets)))
                                            (incf (cdr use))))))
                                 (dolist (el (rest ast))
                                   (relabel el)))
                                (br_if
                                 (let ((label (second ast)))
                                   (cond ((integerp label)
                                          (let ((use (elt block-targets label)))
                                            (incf (cdr use))
                                            (setf (second ast) (car use))))
                                         (t
                                          (let ((use (assoc label block-targets)))
                                            (incf (cdr use))))))
                                 (dolist (el (rest ast))
                                   (relabel el)))
                                ;; Canonicalize integers to signed numbers.
                                (i32.const
                                 (let ((n (second ast)))
                                   (when (>= n #x80000000)
                                     (setf (second ast) (- n #x100000000)))))
                                (i64.const
                                 (let ((n (second ast)))
                                   (when (>= n #x8000000000000000)
                                     (setf (second ast) (- n #x10000000000000000)))))
                                (t
                                 (dolist (el ast)
                                   (relabel el)))))))
                   (relabel body))))
          (map-wasm-functions #'walk wast)))
      ))
  wast)

(defun natural-alignment (op &optional (n 0) (errorp t))
  "Return the natural align of the 'n'th argument of operator 'op, where the
  argument index is an index into the operator fixed argument definitions."
  (declare (type symbol op)
           (fixnum n)
           (optimize (speed 3)))
  (let* ((info (assoc op *wasm-opcodes*))
         (fixed-arg-types (third info))
         (first-type (elt fixed-arg-types n)))
    (cond ((and (consp first-type) (eq (first first-type) 'mem))
           (second first-type))
          (errorp
           (error "Unexpected op: ~S" op))
          (t
           nil))))

;;; There are some distinct memory argument options. Generally expressions are a
;;; list of an operator and argument, so grouping these into a special argument
;;; list would be an exception. Also there might be multiple memory argument and
;;; their options for some operators so that can not be canonicalized to the end
;;; of the argument list like CL style keyword arguments. Thus keeping the
;;; keyword arguments inline seems the best solution, and this helper function
;;; reads the next argument group returning the group and the remained to assist
;;; iterating over the arguments.
(defun parse-memory-access-optional-arguments (args)
  "Helper function to parse the memory option arguments which consist of the
  :offset and :align keyword arguments in that order. The offset, alignment,
  and remaning arguments are returned. If there are no memory options then the
  offset and alignment results are 'nil, and the arguments list is not changed."
  (let ((offset nil)
        (align nil))
    (when (and (consp args)
               (eq (first args) :offset))
      (pop args)
      (assert args)
      (setf offset (pop args))
      (assert (integerp offset)))
    (when (and (consp args)
               (eq (first args) :align))
      (pop args)
      (assert args)
      (setf align (pop args))
      (assert (integerp align)))
    (values offset align args)))

(defun remove-natural-alignments (ast)
  "Remove load/store operation :align arguments when they are equal to the
  natural alignment for the operations. The 'ast is destructively modified."
  (let ((count 0))
    (declare (fixnum count))
    (flet ((walk (name args results locals body)
             (declare (ignore name args results locals))
             (labels ((canonicalize-args (ast)
                        (declare (optimize (speed 3)))
                        (when (consp ast)
                          (dolist (el ast)
                            (canonicalize-args el))
                          (when (and (symbolp (first ast)) (member :align (rest ast)))
                            (let ((new-args nil))
                              (do ((args (rest ast))
                                   (i 0 (1+ i)))
                                  ((endp args))
                                (declare (fixnum i))
                                (let ((first (first args)))
                                  (cond ((symbolp first)
                                         (multiple-value-bind (offset align args*)
                                             (parse-memory-access-optional-arguments args)
                                           (cond ((or offset align)
                                                  (let ((natural-align (natural-alignment (first ast) i nil)))
                                                    (assert natural-align)
                                                    (when offset
                                                      (push :offset new-args)
                                                      (push offset new-args))
                                                    (unless (= align natural-align)
                                                      (push :align new-args)
                                                      (push align new-args)))
                                                  (setf args args*))
                                                 (t
                                                  (push first new-args)
                                                  (assert (eq args* args))
                                                  (setf args (rest args))))))
                                        (t
                                         (push first new-args)
                                         (setf args (rest args))))))
                              (setf (rest ast) (nreverse new-args)))))))
               (canonicalize-args body))))
      (map-wasm-functions #'walk ast))
    (format t "Remove ~d natural :align arguments~%" count))
  ast)

(defun parse-wasm-segment-string (string pos)
  (declare (type simple-string string)
           (fixnum pos))
  (let ((end (length string))
        (bytes nil))
    (assert (> end (+ pos 2)))
    (assert (char= (schar string pos) #\"))
    (do ((pos (1+ pos) (1+ pos)))
        ((>= pos end)
         (error "EOF parsing segment."))
      (let ((c (schar string pos)))
        (case c
          (#\\
           (let ((c1 (schar string (+ pos 1))))
             (case c1
               ((#\" #\' #\\)
                (push (char-code c1) bytes))
               (#\n
                (push #x0a bytes))
               (#\t
                (push #x09 bytes))
               (otherwise
                (push (parse-integer string :start (+ pos 1)
                                     :end (+ pos 3) :radix 16) bytes)
                (incf pos))))
           (incf pos))
          (#\"
           (return-from parse-wasm-segment-string (values (nreverse bytes) (1+ pos))))
          (otherwise
           (let ((code (char-code c)))
             (assert (<= #x20 code #x7f))
             (push code bytes))))))))


(defun import-wast-from-string (string)
  "Read a wast text file from the given string, returning the module s-exp.
  Some rewriting and canonicalization is performed to make it easier to work
  with - this is not intended to be reversible."
  (declare (type simple-string string)
           (optimize (speed 3)))
  (let ((rewrite (with-output-to-string (s)
                   (let ((start 0)
                         (rem (length string)))
                     (declare (fixnum start rem))
                     (flet ((skip-whitespace ()
                              ;; Skip an operator name and the following white space.
                              (do ()
                                  ((<= rem 0))
                                (let ((c (schar string start)))
                                  (when (member c '(#\space #\tab #\linefeed))
                                    (return))
                                  (write-char c s)
                                  (decf rem)
                                  (incf start)))
                              (do ()
                                  ((<= rem 0))
                                 (let ((c (schar string start)))
                                   (unless (member c '(#\space #\tab #\linefeed))
                                     (return))
                                   (write-char c s)
                                   (decf rem)
                                   (incf start)))))
                       (loop
                          (cond ((zerop rem)
                                 (return))
                                ((and (> rem 7)
                                      (string= string "offset="
                                               :start1 start :end1 (+ start 7)))
                                 (write-string ":offset " s)
                                 (incf start 7)
                                 (decf rem 7))
                                ((and (> rem 6)
                                      (string= string "align="
                                               :start1 start :end1 (+ start 6)))
                                 (write-string ":align " s)
                                 (incf start 6)
                                 (decf rem 6))
                                ((and (> rem 11)
                                      (string= string "(segment"
                                               :start1 start :end1 (+ start 8)))
                                 ;; CL escapes strings differently to wasm, so pre-parse
                                 ;; the segments, and use a reader macro.
                                 (let ((pos (position #\" string :start (+ start 8))))
                                   (assert pos)
                                   (do ((i start (1+ i)))
                                       ((>= i pos))
                                     (declare (fixnum i))
                                     (write-char (schar string i) s))
                                   (multiple-value-bind (bytes end)
                                       (parse-wasm-segment-string string pos)
                                     (write-char #\( s)
                                     (dolist (byte bytes)
                                       (format s " ~d" byte))
                                     (write-char #\) s)
                                     (decf rem (- end start))
                                     (setf start end))))
                                ((and (> rem 11)
                                      (string= string "(f32.const"
                                               :start1 start :end1 (+ start 10)))
                                 (skip-whitespace)
                                 (let* ((pos (position #\) string :start start))
                                        (bits (parse-wast-float string :start start :end pos :format 'single-float)))
                                   (format s "#f~x" bits)
                                   (decf rem (- pos start))
                                   (setf start pos)))
                                ((and (> rem 11)
                                      (string= string "(f64.const"
                                               :start1 start :end1 (+ start 10)))
                                 (skip-whitespace)
                                 (let* ((pos (position #\) string :start start))
                                        (bits (parse-wast-float string :start start :end pos :format 'double-float)))
                                   (format s "#d~x" bits)
                                   (decf rem (- pos start))
                                   (setf start pos)))
                                ((and (> rem 11)
                                      (or (string= string "(i32.const"
                                                   :start1 start :end1 (+ start 10))
                                          (string= string "(i64.const"
                                                   :start1 start :end1 (+ start 10))))
                                 ;; Convert to CL Hex interger conventions for reading.
                                 (skip-whitespace)
                                 (cond ((and (char= (schar string start) #\0)
                                             (char= (schar string (1+ start)) #\x))
                                        (setf (schar string start) #\#))
                                       ((and (char= (schar string start) #\-)
                                             (char= (schar string (+ start 1)) #\0)
                                             (char= (schar string (+ start 2)) #\x))
                                        (setf (schar string start) #\#)
                                        (setf (schar string (+ start 1)) #\x)
                                        (setf (schar string (+ start 2)) #\-))))
                                (t
                                 (write-char (aref string start) s)
                                 (incf start)
                                 (decf rem)))))))))
    (remove-natural-alignments
     (import-wast-func-decl
      (let ((*read-default-float-format* 'double-float)
            (*readtable* *wast-readtable*)
            (*wast-float-style* :bits))
        (read-from-string rewrite))))))

(defun import-wast-from-file (file)
  "Import a wast text file, returning the module s-exp."
  (import-wast-from-string (with-output-to-string (o)
                             (with-open-file (s file :direction :input
                                                :element-type 'character)
                               (loop
                                  (let ((line (read-line s nil nil)))
                                    (unless line
                                      (return))
                                    (write-line line o)))))))


;;; Exporting wast.

(defstruct wast-keyword-argument
  key val)

(defmethod print-object ((w wast-keyword-argument) stream)
  (format stream "#k\"~A=~S\"" (wast-keyword-argument-key w)
          (wast-keyword-argument-val w)))

;;; #k"..." reader macro
(defun sharp-k (stream subchar arg)
  (declare (ignore subchar arg))
  (let ((key-str nil))
    (assert (char= (read-char stream t nil t) #\"))
    (loop
       (let ((c (read-char stream t nil t)))
         (when (char= c #\=)
           (return))
         (push c key-str)))
    (setf key-str (coerce (nreverse key-str) 'simple-string))
    (let ((val (read stream t nil t)))
      (make-wast-keyword-argument :key key-str :val val))))
;;;
(set-dispatch-macro-character #\# #\k #'sharp-k *wast-readtable*)


(defstruct wast-double-float
  bits)

(defmethod print-object ((w wast-double-float) stream)
  (let ((bits (wast-double-float-bits w)))
    (ecase *wast-float-style*
      (:number
       (let ((*read-default-float-format* 'double-float))
         (format stream "#d~f" (%make-double-float bits))))
      (:bits
       (format stream "#d~x" bits)))))

(defun sharp-d (stream subchar arg)
  (declare (ignore subchar arg))
  (ecase *wast-float-style*
    (:number
     (error "todo"))
    (:bits
     (let* ((*read-base* 16)
            (bits (read stream t nil t)))
       (assert (integerp bits))
       (make-wast-double-float :bits bits)))))
;;;
(set-dispatch-macro-character #\# #\d #'sharp-d *wast-readtable*)

(defstruct wast-single-float
  bits)

(defmethod print-object ((w wast-single-float) stream)
  (let ((bits (wast-single-float-bits w)))
    (ecase *wast-float-style*
      (:number
       (let ((*read-default-float-format* 'single-float))
         (format stream "#d~f" (%make-single-float bits))))
      (:bits
       (format stream "#f~x" bits)))))

(defun sharp-f (stream subchar arg)
  (declare (ignore subchar arg))
  (ecase *wast-float-style*
    (:number
     (error "todo"))
    (:bits
     (let* ((*read-base* 16)
            (bits (read stream t nil t)))
       (assert (integerp bits))
       (make-wast-single-float :bits bits)))))
;;;
(set-dispatch-macro-character #\# #\f #'sharp-f *wast-readtable*)

(defun export-wast-func-decl (wast)
  "Reverse 'import-wast-func-decl to give wast style function declarations.
  Destructively modifies the 'wast."
  ;; Flush block labels that are 'nil meaning unused.
  (flet ((walk (name args results locals body)
           (declare (ignore name args results locals))
           (labels ((relabel (ast)
                      (when (consp ast)
                        (case (first ast)
                          (tableswitch
                           (assert (rest ast))
                           (when (eq (second ast) 'nil)
                             (pop (rest ast))))
                          (block
                            (assert (rest ast))
                            (unless (second ast)
                              (pop (rest ast))))
                          (loop
                            (cond ((and (eq (second ast) 'nil)
                                        (eq (third ast) 'nil))
                                   (pop (rest ast))
                                   (pop (rest ast)))
                                  ((eq (second ast) 'nil)
                                   (pop (rest ast)))
                                  ((eq (third ast) 'nil)
                                   ;; If there is a single label then it would
                                   ;; be the repeat label but need a break label
                                   ;; so it can't be removed so at least make it
                                   ;; a valid label name.
                                   (setf (third ast) '$unused))))
                          (br_table
                           ;; Flatten.
                           (setf (rest ast) (append (second ast) (rest (rest ast)))))
                          (if_else
                           (assert (= (length ast) 4))
                           (let ((then (third ast))
                                 (else (fourth ast)))
                             (when (or (eq (first then) 'block)
                                       (eq (first else) 'block))
                               ;; Convert to if-then-else style.
                               (cond ((eq (first then) 'block)
                                      (setf (first then) 'then)
                                      (unless (second then)
                                        (pop (rest then))))
                                     (t
                                      (setf (third ast) (list 'then then))))
                               (cond ((eq (first else) 'block)
                                      (setf (first else) 'else)
                                      (unless (second else)
                                        (pop (rest else))))
                                     (t
                                      (setf (fourth ast) (list 'else else))))))
                           (setf (first ast) 'if))
                          (if
                           (assert (= (length ast) 3))
                           (let ((then (third ast)))
                             (when (eq (first then) 'block)
                               ;; Convert to if-then style.
                               (cond ((eq (first then) 'block)
                                      (setf (first then) 'then)
                                      (unless (second then)
                                        (pop (rest then))))
                                     (t
                                      (setf (third ast) (list 'then then)))))))
                          )
                        (dolist (el ast)
                          (relabel el)))))
             (relabel body))))
    (map-wasm-functions #'walk wast))
  ;;
  (flet ((rewrite-func-decl (decl)
           (let ((operands nil))
             (when (second decl)
               (push (cons 'result (second decl)) operands))
             (when (first decl)
               (push (cons 'param (first decl)) operands))
             operands)))
    (dolist (form (rest wast))
      (cond ((not (consp form)))
            ((eq (first form) 'func)
             (let ((args (third form))
                   (results (fourth form))
                   (body (cddddr form))
                   (locals nil))
               ;; Local variables definitions.
               (when (eq (caar body) 'let)
                 (assert (endp (cdr body)))
                 (setf locals (cadar body))
                 (setf body (cddar body)))
               (dolist (local (reverse locals))
                 (push (cons 'local local) body))
               (dolist (result (reverse results))
                 (push (list 'result result) body))
               (dolist (arg (reverse args))
                 (push (cons 'param arg) body))
               (setf (cddr form) body)
               (setf (first form) 'func)))
            ((eq (first form) 'type)
             (let ((decl (rest form)))
               (when (symbolp (first decl))
                 (pop decl))
               (setf decl (first decl))
               (when (eq (first decl) 'func)
                 (setf (rest decl) (rewrite-func-decl (rest decl))))))
            ((eq (first form) 'import)
             (setf (cddddr form) (rewrite-func-decl (cddddr form))))
            ((eq (first form) 'export)
             (ecase (second form)
               (func
                (setf (rest form) (rest (rest form))))
               (memory
                (setf (rest form) (list (third form) 'memory)))))
            )))
  wast)

(defun write-wast-data-segment (bytes stream)
  (write-char #\" stream)
  (dolist (byte bytes)
    (cond ((member byte '(#.(char-code #\") #.(char-code #\') #.(char-code #\\))
                   :test #'=)
           (write-char #\\ stream)
           (write-char (code-char byte) stream))
          ((= byte #x0a)
           (write-char #\\ stream)
           (write-char #\n stream))
          ((= byte #x09)
           (write-char #\\ stream)
           (write-char #\t stream))
          ((<= #x20 byte #x7e)
           (write-char (code-char byte) stream))
          (t
           (format stream "\\~2,'0X" byte))))
  (write-char #\" stream))

(defun export-wast-to-string (wast)
  "Write the 'wast in the wast s-exp format a string and return it. The input
  'wast is not modified."
  ;; Firstly rewrite problematic forms so that will be emitted in a pattern
  ;; that can be fix after emitting a string. The data segment data is split
  ;; out and inserted as strings later.
  (let ((segments nil))
    (labels ((rewrite (ast)
               (cond ((consp ast)
                      (let ((result nil))
                        (dolist (arg ast)
                          (push (rewrite arg) result))
                        (setf ast (nreverse result)))
                      (cond ((eq (first ast) 'segment)
                             ;; Split out the segment data.
                             (push (third ast) segments)
                             ;; Leave a keyword.
                             (setf (third ast) :data))
                            ((and (symbolp (first ast))
                                  (dolist (arg (rest ast) nil)
                                    (when (keywordp arg)
                                      (return t))))
                             ;; Convert keyword arguments to an object.
                             (let ((new-args nil))
                               (do ((args (rest ast) (rest args)))
                                   ((endp args))
                                 (let ((first (first args)))
                                   (cond ((and (keywordp first) (rest args))
                                          (push (make-wast-keyword-argument :key first
                                                                            :val (second args))
                                                new-args)
                                          (setf args (rest args)))
                                         (t
                                          (push first new-args)))))
                               (setf (rest ast) (nreverse new-args))))
                            ((eq (first ast) 'f32.const)
                             (assert (wast-single-float-p (second ast))))
                            ((eq (first ast) 'f64.const)
                             (assert (wast-double-float-p (second ast))))
                            ((eq (first ast) 'i32.const)
                             ;; ml-proto does not like large unsigned integers.
                             (let ((n (second ast)))
                               (when (>= n #x80000000)
                                 (setf (second ast) (- n #x100000000)))))
                            ((eq (first ast) 'i64.const)
                             ;; ml-proto does not like large unsigned integers.
                             (let ((n (second ast)))
                               (when (>= n #x8000000000000000)
                                 (setf (second ast) (- n #x10000000000000000)))))
                            )
                      ast)
                     ((typep ast 'double-float)
                      (make-wast-double-float :bits (%double-float-bits ast)))
                     ((typep ast 'single-float)
                      (make-wast-single-float :bits (%single-float-bits ast)))
                     (t
                      ast))))
      (setf wast (export-wast-func-decl (rewrite wast))))
    (setf segments (nreverse segments))
    ;; Emit the string representation.
    (let ((string (let ((*readtable* *wast-readtable*)
                        (*read-default-float-format* 'double-float)
                        (*print-pretty* t)
                        (*print-right-margin* 132)
                        (*wast-float-style* :number))
                    (with-output-to-string (s)
                      (write wast :stream s)))))
      ;; Patch the output.
      (with-output-to-string (s)
        (let ((start 0)
              (rem (length string)))
          (declare (fixnum start))
          (loop
             (cond ((zerop rem)
                    (return))
                   ((and (> rem 3)
                         (or (string= string "#f" :start1 start :end1 (+ start 2))
                             (string= string "#d" :start1 start :end1 (+ start 2))))
                    (incf start 2)
                    (decf rem 2))
                   ((and (> rem 3)
                         (string= string "#k\"" :start1 start :end1 (+ start 3)))
                    (let ((end (position #\" string :start (+ start 3))))
                      (assert end)
                      (do ((i (+ start 3) (1+ i)))
                          ((>= i end))
                        (write-char (schar string i) s))
                      (incf end)
                      (decf rem (- end start))
                      (setf start end)))
                   ((and (> rem 5)
                         (string= string ":data" :start1 start :end1 (+ start 5)))
                    (write-wast-data-segment (pop segments) s)
                    (incf start 5)
                    (decf rem 5))
                   (t
                    (write-char (schar string start) s)
                    (incf start)
                    (decf rem)))))))))

(defun export-wast-to-file (wast file)
  "Write the 'wast as a wast s-exp file. The input 'wast is not modified."
  (let ((str (export-wast-to-string wast)))
    (with-open-file (s file :direction :output :if-exists :supersede
                       :element-type 'character)
      (write-string str s)))
  nil)

#|

Import/export example:

(defvar *module1*)
(setf *module1* (import-wast-from-file "/tmp/test1.wast"))
(export-wast-to-file *module1* "/tmp/test2.wast")

|#


;;;; Processing.

(defparameter *wasm-predicate-opposites*
  '((i32.eq . i32.ne)
    (i32.ne . i32.eq)
    (i32.lt_s . i32.ge_s)
    (i32.le_s . i32.gt_s)
    (i32.lt_u . i32.ge_u)
    (i32.le_u . i32.gt_u)
    (i32.gt_s . i32.le_s)
    (i32.ge_s . i32.lt_s)
    (i32.gt_u . i32.le_u)
    (i32.ge_u . i32.lt_u)
    (i64.eq . i64.ne)
    (i64.ne . i64.eq)
    (i64.lt_s . i64.ge_s)
    (i64.le_s . i64.gt_s)
    (i64.lt_u . i64.ge_u)
    (i64.le_u . i64.gt_u)
    (i64.gt_s . i64.le_s)
    (i64.ge_s . i64.lt_s)
    (i64.gt_u . i64.le_u)
    (i64.ge_u . i64.lt_u)
    (f32.eq . f32.ne)
    (f32.ne . f32.eq)
    (f64.eq . f64.ne)
    (f64.ne . f64.eq)
    ))

(defun invert-predicate (predicate)
  "Invert the logic of the 'predicate expression, attempting to remove a
  comparison to zero, or changing a test operator, otherwise adding a not-zero
  test. The inverted expression is returned and the original is not modified."
  (cond ((and (eq (first predicate) 'i32.eq)
              (equalp (third predicate) '(i32.const 0)))
         (second predicate))
        ((and (eq (first predicate) 'i32.eq)
              (equalp (second predicate) '(i32.const 0)))
         (third predicate))
        (t
         (let* ((op (first predicate))
                (opposite (cdr (assoc op *wasm-predicate-opposites*))))
           (cond (opposite
                  (assert (= (length predicate) 3))
                  `(,opposite ,(second predicate) ,(third predicate)))
                 (t
                  `(i32.eq ,predicate (i32.const 0))))))))

(defun clear-unused-block-labels (ast)
  "Clear blocks labels that are not referenced. Destructively modifies
  the 'ast."
  (let (;; Statistics counter.
        (removed-labels-count 0))
    (flet ((walk (name args results locals body)
             (declare (ignore name args results locals))
             (let ((block-targets nil))
               (labels ((clear-unused-block-labels* (ast)
                          (when (consp ast)
                            (case (first ast)
                              (block
                               (assert (symbolp (second ast)))
                               (let ((label (second ast)))
                                 (when label
                                   (push (cons label 0) block-targets))
                                 (dolist (expression (rest (rest ast)))
                                   (clear-unused-block-labels* expression))
                                 (when label
                                   (let* ((binding (pop block-targets))
                                          (num-uses (cdr binding)))
                                     ;; Check that that 'block-targets stack has been restored.
                                     (assert (eq (car binding) label))
                                     (cond ((zerop num-uses)
                                            ;; Remove the label from the block.
                                            (incf removed-labels-count)
                                            (setf (second ast) nil))
                                           (t
                                            (let* ((last (last ast))
                                                   (last-expression (first last)))
                                              (when (and (consp last-expression)
                                                         (eq (first last-expression) 'br)
                                                         (eq (second last-expression) label))
                                                ;; Block ending is a br out of the block, so eliminate the label.
                                                (cond ((cddr last-expression)
                                                       ;; A 'br' with an expression. Expect just one value.
                                                       (assert (not (cdddr last-expression)))
                                                       (setf (first last) (third last-expression)))
                                                      (t
                                                       ;; No expression, insert a nop?
                                                       (setf (first last) '(nop))))
                                                (decf num-uses)
                                                ;; If now unused then remove the label.
                                                (when (zerop num-uses)
                                                  (incf removed-labels-count)
                                                  (setf (second ast) nil))))))))))
                              (loop
                               (let ((break-label (second ast))
                                     (repeat-label (third ast)))
                                 (when break-label
                                   (push (cons break-label 0) block-targets))
                                 (when repeat-label
                                   (push (cons repeat-label 0) block-targets))
                                 (dolist (expression (rest (rest (rest ast))))
                                   (clear-unused-block-labels* expression))
                                 (when repeat-label
                                   (assert (eq (car (pop block-targets)) repeat-label)))
                                 (when break-label
                                   (assert (eq (car (pop block-targets)) break-label)))
                                 ))
                              (tableswitch
                               (let ((break-label (second ast)))
                                 (when break-label
                                   (push (cons break-label 0) block-targets))
                                 (dolist (expression (rest (rest ast)))
                                   (clear-unused-block-labels* expression))
                                 (when break-label
                                   (assert (eq (car (pop block-targets)) break-label)))))
                              (br_table
                               (destructuring-bind (targets default key)
                                   (rest ast)
                                 (clear-unused-block-labels* key)
                                 (dolist (label targets)
                                   (assert (and label (symbolp label)))
                                   (let ((binding (assoc label block-targets)))
                                     (cond (binding
                                            ;; Found a reference to a block label within scope.
                                            (incf (cdr binding)))
                                           (t
                                            (warn "Unknown br_table target label: ~S" label)))))
                                 (assert (and default (symbolp default)))
                                 (let ((binding (assoc default block-targets)))
                                   (cond (binding
                                          ;; Found a reference to a block label within scope.
                                          (incf (cdr binding)))
                                         (t
                                          (warn "Unknown br_table default label: ~S" default))))))
                              ((br br_if)
                               (let ((label (second ast)))
                                 (assert (and label (symbolp label)))
                                 (let ((binding (assoc label block-targets)))
                                   (cond (binding
                                          ;; Found a reference to a block label within scope.
                                          (incf (cdr binding)))
                                         (t
                                          (warn "Unknown label: ~S" label)))))
                               (dolist (el (rest (rest ast)))
                                 (clear-unused-block-labels* el)))
                              (otherwise
                               ;; Some other form - walk the elements.
                               (dolist (el ast)
                                 (clear-unused-block-labels* el)))
                              ))))
                 (clear-unused-block-labels* body)))))
      (map-wasm-functions #'walk ast))
    (format t "Cleared ~d unused block labels~%" removed-labels-count))
  nil)

(defun flatten-blocks (ast)
  "Flatten unnecessary blocks, blocks with no label and used in a
  context that already permits a list of expressions."
  (let (;; Statistics counter.
        (flattened-blocks-count 0))
    (flet ((walk (name args results locals body)
             (declare (ignore name args results locals))
             (labels ((flatten (bexp)
                        ;; Flatten child block into the 'bexp list of block expressions.
                        ;; Expecting a cons to be updated if necessary.
                        (assert (consp bexp))
                        (do ((bexp bexp (rest bexp)))
                            ((endp bexp))
                          (let ((first (first bexp)))
                            (when (consp first)
                              (walk first)
                              (when (and (eq (first first) 'block)
                                         ;; If not a br target then flatten.
                                         (not (second first)))
                                ;; Insert it into the current block expression list.
                                (incf flattened-blocks-count)
                                (setf (first bexp) (third first))
                                (setf (rest (last first)) (rest bexp))
                                (setf (rest bexp) (rest (rest (rest first)))))))))
                      (walk (ast)
                        (when (consp ast)
                          (let ((first (first ast)))
                            (cond ((eq first 'block)
                                   (let ((label (second ast)))
                                     (assert (symbolp label))
                                     (flatten (rest (rest ast)))
                                     (when (and (not label)
                                                (= (length ast) 3))
                                       ;; Only one expression, flatten.
                                       (let ((exp (third ast)))
                                         (setf (first ast) (first exp))
                                         (setf (rest ast) (rest exp))))))
                                  ((eq first 'loop)
                                   (assert (symbolp (second ast)))
                                   (assert (symbolp (third ast)))
                                   (flatten (rest (rest (rest ast)))))
                                  ((and (eq first 'case)
                                        (rest (rest ast)))
                                   (assert (symbolp (second ast)))
                                   (flatten (rest (rest ast))))
                                  ((eq first 'br_table)
                                   (assert (= (length ast) 4))
                                   (flatten (fourth ast)))
                                  ((eq first 'let)
                                   (flatten (rest (rest ast))))
                                  ((member first '(when unless))
                                   (walk (second ast))
                                   (flatten (rest (rest ast))))
                                  (t
                                   (dolist (el ast)
                                     (walk el)))))))
                      )
               (when body
                 (flatten body)))))
      (map-wasm-functions #'walk ast))
    (format t "Flattened ~d blocks~%" flattened-blocks-count))
  nil)


(defun canonicalize-block-br-diamonds (ast)
  "Canonicalize block-br_if diamond patterns to `if_else, or 'if.
  Destructively modifies the 'ast."
  (let (;; Statistics counter.
        (canonicalized-count 0)
        (canonicalized-ifs-count 0))
    (flet ((walk (name args results locals body)
             (declare (ignore name args results locals))
             (labels ((canonicalize (ast)
                        (cond ((not (consp ast)))
                              ((and (eq (first ast) 'block)
                                    (second ast))
                               (let ((block-label (second ast)))
                                 (assert (symbolp block-label))
                                 (do ((exps (cddr ast) (rest exps)))
                                     ((endp exps))
                                   (let ((inner-block (first exps)))
                                     (assert (consp inner-block))
                                     (cond ((and (eq (first inner-block) 'block)
                                                 (second inner-block))
                                            (let ((inner-label (second inner-block))
                                                  (br-if (third inner-block))
                                                  (inner-br (first (last inner-block))))
                                              (assert (symbolp inner-label))
                                              (cond ((and (eq (first br-if) 'br_if)
                                                          (eq (second br-if) inner-label)
                                                          (= (length br-if) 3)
                                                          (eq (first inner-br) 'br)
                                                          (eq (second inner-br) block-label))
                                                     (let ((inner-path (cdddr inner-block))
                                                           (outer-path (rest exps))
                                                           (predicate (third br-if)))
                                                       (canonicalize predicate)
                                                       (setf inner-path (subseq inner-path 0 (1- (length inner-path))))
                                                       ;; Retain the labels because it would not be
                                                       ;; valid to remove them unless there were no
                                                       ;; other uses and this is not being checked here.
                                                       (setf inner-path `((block ,block-label (block ,inner-label ,@inner-path))))
                                                       (setf outer-path `((block ,block-label ,@outer-path)))
                                                       ;; New opportunities might now be obvious.
                                                       (canonicalize inner-path)
                                                       (canonicalize outer-path)
                                                       (cond ((and (eq (first predicate) 'i32.eq)
                                                                   (equalp (third predicate) '(i32.const 0)))
                                                              ;; Negate the predicate and swap the paths.
                                                              (setf predicate (second predicate))
                                                              (rotatef inner-path outer-path))
                                                             ((and (eq (first predicate) 'i32.eq)
                                                                   (equalp (second predicate) '(i32.const 0)))
                                                              ;; Negate the predicate and swap the paths.
                                                              (setf predicate (third predicate))
                                                              (rotatef inner-path outer-path)))
                                                       ;; Keep the outer label, just in case
                                                       ;; there are any references above,
                                                       ;; but shadow it for the inner blocks
                                                       ;; to help make it easier for them to
                                                       ;; be optimized.
                                                       (setf (first exps) `(if_else ,predicate ,@outer-path ,@inner-path))
                                                       (setf (rest exps) nil)
                                                       (incf canonicalized-count)
                                                       ))
                                                    (t
                                                     (canonicalize inner-block)))))
                                           ((and (eq (first inner-block) 'br_if)
                                                 (eq (second inner-block) block-label)
                                                 (= (length inner-block) 3))
                                            ;; Got an 'if pattern.
                                            (let ((predicate (third inner-block))
                                                  (inner-block `(block ,block-label ,@(rest exps))))
                                              (canonicalize predicate)
                                              ;; New opportunities might now be obvious.
                                              (canonicalize inner-block)
                                              (setf (first exps) `(if ,(invert-predicate predicate) ,inner-block))
                                              (setf (rest exps) nil))
                                            (incf canonicalized-ifs-count))
                                           (t
                                            (canonicalize inner-block))
                                           )))))
                              (t
                               (dolist (el ast)
                                 (canonicalize el))))))
               (canonicalize body))))
      (map-wasm-functions #'walk ast))
    (format t "Canonicalized ~d block-br diamonds and ~d 'if patterns~%" canonicalized-count canonicalized-ifs-count))
  nil)


#|
;;; Example usage to convert the br_if style output of the llvm backend to
;;; 'if_else and 'if where possible and write two binary files form comparison.

(defvar *module1*)
(setf *module1* (import-wast-from-file "/tmp/test.wast"))
(show-wast-opcode-counts *module1*)
(write-wasm-to-file *module1* :file "/tmp/test.wasm")

(canonicalize-block-br-diamonds *module1*)
(clear-unused-block-labels *module1*)
(flatten-blocks *module1*)
(show-wast-opcode-counts *module1*)
(write-wasm-to-file *module1* :file "/tmp/test2.wasm")

|#



(defun count-wast-opcodes (wast)
  (let ((table (make-hash-table)))
    (flet ((count-fn-opcodes (name args results locals body)
             (declare (ignore name args results locals))
             (labels ((count-opcodes (list)
                        (when (consp list)
                          (let ((op (first list)))
                            (when (symbolp op)
                              (incf (gethash op table 0)))
                            (dolist (el list)
                              (count-opcodes el))))))
               (count-opcodes body))))
      (map-wasm-functions #'count-fn-opcodes wast))
    table))

(defun sort-wast-opcode-counts (table)
  (let ((c nil)
        (total 0))
    (maphash #'(lambda (key val) (push (cons key val) c)) table)
    (setf c (sort c #'> :key 'cdr))
    (dolist (e c)
      (incf total (cdr e)))
    (values c total)))

(defun show-wast-opcode-counts (wast)
  (multiple-value-bind (c total)
      (sort-wast-opcode-counts (count-wast-opcodes wast))
    (let ((r 0))
      (dolist (e c)
        (incf r (cdr e))
        (format t "~30S ~5d ~8,2f~%" (car e) (cdr e) (* 100 (/ (cdr e) total)))))))


;;;; Writing the wasm binary format.

;;; Table of extended operators.
;;;
;;; For example:
;;;  (set/c local const) - set a local variable to an immediate label and constant.
;;;  (set/c local local) - copy one a local variable to another with immediate labels.
;;;  (br/c branch const) - break to an immediate label returning an immediate constant.
;;;
(defparameter *opcode-table*
  `((i32.set/l nil (i32-local i32-local) nil (i32))
    (i32.set/c nil (i32-local i32-imm) nil (i32))
    (i32.br/l nil (branch i32-local) nil e)
    (i32.br/c nil (branch i32-imm) nil e)
    (f64.set/l nil (f64-local f64-local) nil (f64))
    (f64.set/c nil (f64-local f64-imm) nil (f64))
    (f64.br/l nil (branch f64-local) nil e)
    (f64.br/c nil (branch f64-imm) nil e)
    (br/n nil (branch) nil e)

    ,@(let ((ops nil))
        (dolist (prefix '(i32.add i32.xor i32.or i32.and i32.mul
                          i32.sub
                          i32.eq i32.ne i32.lt_u i32.gt_u i32.gt_s i32.lt_s i32.ge_u i32.le_u i32.ge_s i32.le_s
                          i32.shl i32.shr_u i32.shr_s))
          (dolist (suffix '((/lc nil (i32-local i32-imm) nil (i32))
                            (/cl nil (i32-imm i32-local) nil (i32))
                            (/ll nil (i32-local i32-local) nil (i32))
                            (/sc nil (i32 i32-imm) nil (i32))
                            (/cs nil (i32-imm i32) nil (i32))
                            (/ls nil (i32-local i32) nil (i32))))
            (let ((name (intern (format nil "~A~A" prefix (first suffix)) :common-lisp-user)))
              (push `(,name ,@(rest suffix)) ops))))
        (nreverse ops))

    ,@(let ((ops nil))
        (dolist (prefix '(f64.ne))
          (dolist (suffix '((/lc nil (f64-local f64-imm) nil (f64))
                            (/cl nil (f64-imm f64-local) nil (f64))
                            (/ll nil (f64-local f64-local) nil (f64))
                            (/sc nil (f64 f64-imm) nil (f64))
                            (/cs nil (f64-imm f64) nil (f64))
                            (/ls nil (f64-local f64) nil (f64))))
            (let ((name (intern (format nil "~A~A" prefix (first suffix)) :common-lisp-user)))
              (push `(,name ,@(rest suffix)) ops))))
        (nreverse ops))

    ,@(let ((ops nil))
        (dolist (prefix '(i32.load i32.load16_u i32.load16_s i32.load8_u i32.load8_s))
          (dolist (suffix '((/c nil ((mem 4) i32-imm) nil (i32))
                            (/l nil ((mem 4) i32-local) nil (i32))
                            (-add/lc nil ((mem 4) i32-local i32-imm) nil (i32))
                            (-add/ll nil ((mem 4) i32-local i32-local) nil (i32))
                            (-add/sc nil ((mem 4) i32 i32-imm) nil (i32))
                            (-add/ls nil ((mem 4) i32-local i32) nil (i32))
                            (-add/sl nil ((mem 4) i32 i32-local) nil (i32))))
            (let ((name (intern (format nil "~A~A" prefix (first suffix)) :common-lisp-user)))
              (push `(,name ,@(rest suffix)) ops))))
        (nreverse ops))

    ,@(let ((ops nil))
        (dolist (prefix '(f64.load))
          (dolist (suffix '((/c nil ((mem 8) i32-imm))
                            (/l nil ((mem 8) i32-local))
                            (-add/lc nil ((mem 8) i32-local f64-imm))
                            (-add/ll nil ((mem 8) i32-local i32-local))
                            (-add/sc nil ((mem 8) f64 f64-imm))
                            (-add/ls nil ((mem 8) i32-local f64))
                            (-add/sl nil ((mem 8) f64 i32-local))))
            (let ((name (intern (format nil "~A~A" prefix (first suffix)) :common-lisp-user)))
              (push `(,name ,@(rest suffix)) ops))))
        (nreverse ops))

    ,@(let ((ops nil))
        (dolist (prefix '(i32.store i32.store16 i32.store8))
          (dolist (suffix '((/cc nil ((mem 4) i32-imm i32-imm) nil (i32))
                            (/lc nil ((mem 4) i32-local i32-imm) nil (i32))
                            (/cl nil ((mem 4) i32-imm i32-local) nil (i32))
                            (/ll nil ((mem 4) i32-local i32-local) nil (i32))
                            (/cs nil ((mem 4) i32-imm i32) nil (i32))
                            (/ls nil ((mem 4) i32-local i32) nil (i32))
                            (/sc nil ((mem 4) i32 i32-imm) nil (i32))
                            (/sl nil ((mem 4) i32 i32-local) nil (i32))))
            (let ((name (intern (format nil "~A~A" prefix (first suffix)) :common-lisp-user)))
              (push `(,name ,@(rest suffix)) ops)))
          (dolist (suffix '((-add/lc nil ((mem 4) i32-local i32-imm i32) nil (i32))
                            (-add/ll nil ((mem 4) i32-local i32-local i32) nil (i32))
                            (-add/sc nil ((mem 4) i32 i32-imm i32) nil (i32))
                            (-add/ls nil ((mem 4) i32-local i32 i32) nil (i32))
                            (-add/sl nil ((mem 4) i32 i32-local i32) nil (i32))
                            (/sc-add/lc nil ((mem 4) i32-local i32-imm i32-imm) nil (i32))
                            (/sc-add/ll nil ((mem 4) i32-local i32-local i32-imm) nil (i32))
                            (/sc-add/sc nil ((mem 4) i32 i32-imm i32-imm) nil (i32))
                            (/sc-add/ls nil ((mem 4) i32-local i32 i32-imm) nil (i32))
                            (/sc-add/sl nil ((mem 4) i32 i32-local i32-imm) nil (i32))
                            (/sl-add/lc nil ((mem 4) i32-local i32-imm i32-local) nil (i32))
                            (/sl-add/ll nil ((mem 4) i32-local i32-local i32-local) nil (i32))
                            (/sl-add/sc nil ((mem 4) i32 i32-imm i32-local) nil (i32))
                            (/sl-add/ls nil ((mem 4) i32-local i32 i32-local) nil (i32))
                            (/sl-add/sl nil ((mem 4) i32 i32-local i32-local) nil (i32))))
            (let ((name (intern (format nil "~A~A" prefix (first suffix)) :common-lisp-user)))
              (push `(,name ,@(rest suffix)) ops))))

        (dolist (prefix '(f64.store))
          (dolist (suffix '((/cc nil ((mem 8) i32-imm f64-imm) nil (f64))
                            (/lc nil ((mem 8) local f64-imm) nil (f64))
                            (/cl nil ((mem 8) i32-imm f64-local) nil (f64))
                            (/ll nil ((mem 8) i32-local f64-local) nil (f64))
                            (/cs nil ((mem 8) i32-imm f64) nil (f64))
                            (/ls nil ((mem 8) i32-local f64) nil (f64))
                            (/sc nil ((mem 8) i32 f64-imm) nil (f64))
                            (/sl nil ((mem 8) i32 f64-local) nil (f64))))
            (let ((name (intern (format nil "~A~A" prefix (first suffix)) :common-lisp-user)))
              (push `(,name ,@(rest suffix)) ops)))
          (dolist (suffix '((-add/lc nil ((mem 8) i32-local i32-imm f64) nil (f64))
                            (-add/ll nil ((mem 8) i32-local i32-local f64) nil (f64))
                            (-add/sc nil ((mem 8) i32 i32-imm f64) nil (f64))
                            (-add/ls nil ((mem 8) i32-local i32 f64) nil (f64))
                            (-add/sl nil ((mem 8) i32 i32-local f64) nil (f64))
                            (/sc-add/lc nil ((mem 8) i32-local i32-imm f64-imm) nil (f64))
                            (/sc-add/ll nil ((mem 8) i32-local i32-local f64-imm) nil (f64))
                            (/sc-add/sc nil ((mem 8) i32 i32-imm f64-imm) nil (f64))
                            (/sc-add/ls nil ((mem 8) i32-local i32 f64-imm) nil (f64))
                            (/sc-add/sl nil ((mem 8) i32 i32-local f64-imm) nil (f64))
                            (/sl-add/lc nil ((mem 8) i32-local i32-imm f64-local) nil (f64))
                            (/sl-add/ll nil ((mem 8) i32-local i32-local f64-local) nil (f64))
                            (/sl-add/sc nil ((mem 8) i32 i32-imm f64-local) nil (f64))
                            (/sl-add/ls nil ((mem 8) i32-local i32 f64-local) nil (f64))
                            (/sl-add/sl nil ((mem 8) i32 i32-local f64-local) nil (f64))))
            (let ((name (intern (format nil "~A~A" prefix (first suffix)) :common-lisp-user)))
              (push `(,name ,@(rest suffix)) ops)))
          )
        (nreverse ops))
    ))

(defun find-wasm-signatures (ast)
  "Find the function signatures that the sexpr-wasm binary encoder emits."
  (let ((sigs nil))
    ;; Firstly the types, without de-duping.
    (dolist (fn ast)
      (when (and (consp fn) (eq (first fn) 'type))
        (setf fn (rest fn))
        (when (symbolp (first fn))
          (setf fn (rest fn)))
        (let ((fn (first fn)))
          (assert (eq (first fn) 'func))
          (let ((args (second fn))
                (results (third fn)))
            (assert (<= (length results) 1))
            (push (cons (first results) args) sigs)))))
    ;; Next the imports, with de-duping.
    (dolist (fn ast)
      (when (and (consp fn) (eq (first fn) 'import))
        (let ((args (fifth fn))
              (results (sixth fn)))
          (assert (<= (length results) 1))
          (pushnew (cons (first results) args) sigs :test 'equalp))))
    ;; Then the functions, with de-duping.
    (dolist (fn ast)
      (when (and (consp fn) (eq (first fn) 'func))
        (let ((args (third fn))
              (arg-types nil)
              (results (fourth fn)))
          (assert (<= (length results) 1))
          (dolist (a args)
            (push (second a) arg-types))
          (let ((sig `(,(first results) ,@(nreverse arg-types))))
            (pushnew sig sigs :test 'equalp)))))
    (nreverse sigs)))

(defun compute-locals-map (fn)
  "Return an list of the argument names and local variable names in
  the order they appear and would be indexed in the binary encoding."
  (assert (eq (first fn) 'func))
  (let* ((args (third fn))
         (body (cddddr fn))
         (locals (cond ((eq (caar body) 'let)
                        (assert (not (cdr body)))
                        (second (first body)))
                       (t
                        nil)))
         (map nil))
    (dolist (arg args)
      (let ((name (first arg)))
        (assert name)
        (push name map)))
    (dolist (local locals)
      (let ((name (first local)))
        (assert name)
        (push name map)))
    (nreverse map)))

(defvar *wasm-source-map* nil)

(defun write-wasm (wast &key (reorder-opcodes nil) (inline t) (names-p t))
  "Write the 'wast to a byte array.

  A primitive map is generated and stored in *wasm-source-map* that
  parallels the wast structure and includes the file position of many of the
  elements written."
  (let (;; Table mapping the opcode name to an index.
        (opcode-table (make-hash-table))
        ;;
        (memory-sections nil)
        (data-segments nil)
        ;;
        ;; Ordered list of the imports.
        (imports-list nil)
        ;; Ordered list of the imports and functions.
        (imports-and-functions-list nil)
        ;; Ordered list of the functions.
        (functions-list nil)
        ;; Ordered list indirect call signatures.
        (indirect-call-types nil)
        ;; Exports list.
        (exported-functions nil)
        ;;
        ;; Function table
        (function-table nil)
        ;;
        ;; Start function name.
        (start-function nil)
        ;;
        (sections nil)
        ;;
        (signatures (find-wasm-signatures wast))
        ;;
        (export-memory-p nil)
        ;;
        ;; The names or function arguments and local variables, when
        ;; the names sections is to be written.
        (locals-names nil)
        )
    ;;
    (cond (reorder-opcodes
           (let ((counts (sort-wast-opcode-counts (count-wast-opcodes wast))))
             (dotimes (i (length counts))
               (let* ((name (car (elt counts i)))
                      (info (or (assoc name *wasm-opcodes*)
                                (assoc name *opcode-table*))))
                  (setf (gethash name opcode-table) (list* name i (cddr info)))))))
          (t
           (dolist (info *wasm-opcodes*)
             (setf (gethash (first info) opcode-table) info))))
    ;;
    (assert (eq (first wast) 'module))
    (dolist (el (rest wast))
      (ecase (first el)
        (memory
         (push (rest el) memory-sections))
        (type
         (push (second el) indirect-call-types))
        (import
         (push (second el) imports-list)
         (push (second el) imports-and-functions-list))
        (func
         (push (second el) functions-list)
         (push (second el) imports-and-functions-list))
        (table
         (assert (not function-table))
         (setf function-table (rest el)))
        (export
         (ecase (second el)
           (func
            (push (cons (fourth el) (third el)) exported-functions))
           (memory
            (setf export-memory-p t))))
        (start
         (assert (= (length el) 2))
         (assert (not start-function))
         (setf start-function (second el)))
        ))
    (setf memory-sections (nreverse memory-sections))
    (setf imports-list (nreverse imports-list))
    (setf exported-functions (nreverse exported-functions))
    (setf functions-list (nreverse functions-list))
    (setf imports-and-functions-list (nreverse imports-and-functions-list))
    (setf indirect-call-types (nreverse indirect-call-types))
    ;;
    (labels ((imports-index (fn)
               (let ((index (position fn imports-list)))
                 (assert index)
                 index))
             (functions-index (fn)
               (declare (type symbol fn))
               (let ((index (position fn functions-list)))
                 (assert index)
                 index))
             (indirect-call-type (fn)
               (let ((index (position fn indirect-call-types)))
                 (assert index)
                 index))
             (write-leb128-u32* (n bytes)
               (declare (type (unsigned-byte 32) n)
                        (type (array (unsigned-byte 8) (*)) bytes))
               (loop
                  (when (< n #x80)
                    (vector-push-extend n bytes)
                    (return))
                  (vector-push-extend (logior (logand n #x7f) #x80) bytes)
                  (setf n (ash n -7))))
             (write-leb128-i32* (n bytes)
               (declare (type (signed-byte 32) n)
                        (type (array (unsigned-byte 8) (*)) bytes))
               (loop
                  (when (<= #x-40 n #x3f)
                    (vector-push-extend (logand n #x7f) bytes)
                    (return))
                  (vector-push-extend (logior (logand n #x7f) #x80) bytes)
                  (setf n (ash n -7))))
             #+nil                      ; not used
             (write-leb128-u64* (n bytes)
               (declare (type (unsigned-byte 64) n)
                        (type (array (unsigned-byte 8) (*)) bytes))
               (loop
                  (when (< n #x80)
                    (vector-push-extend n bytes)
                    (return))
                  (vector-push-extend (logior (logand n #x7f) #x80) bytes)
                  (setf n (ash n -7))))
             (write-leb128-i64* (n bytes)
               (declare (type (signed-byte 64) n)
                        (type (array (unsigned-byte 8) (*)) bytes))
               (loop
                  (when (<= #x-40 n #x3f)
                    (vector-push-extend (logand n #x7f) bytes)
                    (return))
                  (vector-push-extend (logior (logand n #x7f) #x80) bytes)
                  (setf n (ash n -7))))
             (write-leb128-u32 (n bytes)
               (declare (type (array (unsigned-byte 8) (*)) bytes))
               (let ((start (length bytes)))
                 (write-leb128-u32* n bytes)
                 `(:leb128-u32 ,start ,(length bytes) ,n)))
             (write-leb128-i32 (n bytes)
               (declare (type (array (unsigned-byte 8) (*)) bytes))
               (let ((start (length bytes)))
                 (write-leb128-i32* n bytes)
                 `(:leb128-i32 ,start ,(length bytes) ,n)))
             #+nil                      ; not used
             (write-leb128-u64 (n bytes)
               (declare (type (array (unsigned-byte 8) (*)) bytes))
               (let ((start (length bytes)))
                 (write-leb128-u64* n bytes)
                 `(:leb128-u64 ,start ,(length bytes) ,n)))
             (write-leb128-i64 (n bytes)
               (declare (type (array (unsigned-byte 8) (*)) bytes))
               (let ((start (length bytes)))
                 (write-leb128-i64* n bytes)
                 `(:leb128-i64 ,start ,(length bytes) ,n)))
             (write-opcode (op bytes)
               (declare (type (array (unsigned-byte 8) (*)) bytes))
               (let ((start (length bytes))
                     (index (second (gethash op opcode-table))))
                 (unless index
                   (warn "Unknown operator: ~S~%" op)
                   (setf index 0))
                 (cond (reorder-opcodes
                        (write-leb128-u32* index bytes))
                       (t
                        (vector-push-extend index bytes)))
                 `(:opcode ,start ,(length bytes) ,op)))
             (inline-arg (node)
               (cond ((eq inline t)
                      t)
                     ((eq inline nil)
                      nil)
                     (t
                      (gethash node inline))))
             (write-u8 (n bytes)
               (declare (type (array (unsigned-byte 8) (*)) bytes))
               (let ((start (length bytes)))
                 (vector-push-extend n bytes)
                 `(:u8 ,start ,(length bytes) ,n)))
             (write-u16 (n bytes)
               (declare (type (array (unsigned-byte 8) (*)) bytes))
               (let ((start (length bytes)))
                 (vector-push-extend (ldb (byte 8 0) n) bytes)
                 (vector-push-extend (ldb (byte 8 8) n) bytes)
                 `(:u16 ,start ,(length bytes) ,n)))
             (write-u32 (n bytes)
               (declare (type (array (unsigned-byte 8) (*)) bytes))
               (let ((start (length bytes)))
                 (vector-push-extend (ldb (byte 8 0) n) bytes)
                 (vector-push-extend (ldb (byte 8 8) n) bytes)
                 (vector-push-extend (ldb (byte 8 16) n) bytes)
                 (vector-push-extend (ldb (byte 8 24) n) bytes)
                 `(:u32 ,start ,(length bytes) ,n)))
             #+nil                      ; not used
             (write-u64 (n bytes)
               (declare (type (array (unsigned-byte 8) (*)) bytes))
               (let ((start (length bytes)))
                 (vector-push-extend (logand n #xff) bytes)
                 (vector-push-extend (ldb (byte 8 8) n) bytes)
                 (vector-push-extend (ldb (byte 8 16) n) bytes)
                 (vector-push-extend (ldb (byte 8 24) n) bytes)
                 (vector-push-extend (ldb (byte 8 32) n) bytes)
                 (vector-push-extend (ldb (byte 8 40) n) bytes)
                 (vector-push-extend (ldb (byte 8 48) n) bytes)
                 (vector-push-extend (ldb (byte 8 56) n) bytes)
                 `(:u64 ,start ,(length bytes) ,n)))
             (write-f32 (n bytes)
               (declare (type (array (unsigned-byte 8) (*)) bytes))
               (let ((start (length bytes)))
                 (let ((bits (etypecase n
                               (integer
                                n)
                               (wast-single-float
                                (wast-single-float-bits n))
                               (single-float
                                (%single-float-bits n)))))
                   (vector-push-extend (logand bits #xff) bytes)
                   (vector-push-extend (ldb (byte 8 8) bits) bytes)
                   (vector-push-extend (ldb (byte 8 16) bits) bytes)
                   (vector-push-extend (ldb (byte 8 24) bits) bytes))
                 `(:f32 ,start ,(length bytes) ,n)))
             (write-f64 (n bytes)
               (declare (type (array (unsigned-byte 8) (*)) bytes))
               (let ((start (length bytes)))
                 (let ((bits (etypecase n
                               (integer
                                n)
                               (wast-double-float
                                (wast-double-float-bits n))
                               (double-float
                                (%double-float-bits n)))))
                   (vector-push-extend (logand bits #xff) bytes)
                   (vector-push-extend (ldb (byte 8 8) bits) bytes)
                   (vector-push-extend (ldb (byte 8 16) bits) bytes)
                   (vector-push-extend (ldb (byte 8 24) bits) bytes)
                   (vector-push-extend (ldb (byte 8 32) bits) bytes)
                   (vector-push-extend (ldb (byte 8 40) bits) bytes)
                   (vector-push-extend (ldb (byte 8 48) bits) bytes)
                   (vector-push-extend (ldb (byte 8 56) bits) bytes))
                 `(:f64 ,start ,(length bytes) ,n)))
             (write-wasm-string (str bytes)
               (declare (type (array (unsigned-byte 8) (*)) bytes))
               (let ((string* nil))
                 ;; TODO utf-8
                 (push (write-leb128-u32 (length str) bytes) string*)
                 (dotimes (i (length str))
                   (push (write-u8 (char-code (schar str i)) bytes) string*))
                 `(:string ,(nreverse string*))))
             (write-section-marker (n bytes)
               (declare (type (array (unsigned-byte 8) (*)) bytes))
               (let ((start (length bytes)))
                 (write-wasm-string n bytes)
                 `(:section-id ,start ,(length bytes) ,n)))
             (wasm-type-code (type)
               (ecase type
                 ((nil) 0)
                 (i32 1)
                 (i64 2)
                 (f32 3)
                 (f64 4)))
             )
      (let ((module-bytes (make-array '(0) :adjustable t :fill-pointer t
                                      :element-type '(unsigned-byte 8))))
        ;; The magic number
        (write-u32 #x6d736100 module-bytes)
        ;; Version.
        (write-u32 10 module-bytes)
        ;;
        (macrolet ((with-section ((bytes map name) &body body)
                     `(let* ((,map nil)
                             (bytes (make-array '(0) :adjustable t :fill-pointer t
                                                :element-type '(unsigned-byte 8))))
                        (let ((,bytes bytes))
                          (push (write-section-marker ,name ,bytes) ,map)
                          ,@body)
                        (let ((size (write-leb128-u32 (length bytes) module-bytes)))
                          (dotimes (i (length bytes))
                            (vector-push-extend (aref bytes i) module-bytes))
                          (push `((:section ,(length bytes))
                                  ,size
                                  ,@(nreverse ,map))
                                sections)))
                     ))
          ;; Write the optional signatures section.
          (when (plusp (length signatures))
            (with-section (section map "signatures")
              (push (write-leb128-u32 (length signatures) section) map)
              (dolist (sig signatures)
                ;; Num. args types.
                (push (write-leb128-u32 (1- (length sig)) section) map)
                (dolist (o sig)
                  (let ((v (wasm-type-code o)))
                    (push (write-u8 v section) map))))))
          ;;
          ;; Imports section.
          (when imports-list
            (with-section (section map "import_table")
              ;; Number of imports.
              (push (write-leb128-u32 (length imports-list) section) map)
              (dolist (fn wast)
                (when (consp fn)
                  (when (eq (first fn) 'import)
                    (destructuring-bind (module-name function-name params results)
                        (rest (rest fn))
                      (let* ((sig `(,(first results) ,@params))
                             (signum (position sig signatures :test 'equalp)))
                        (assert signum)
                        (let ((function* nil))
                          (push (write-leb128-u32 signum section) function*)
                          (push (write-wasm-string module-name section) function*)
                          (push (write-wasm-string function-name section) function*)
                          (push (nreverse function*) map)))))))))
          ;;
          ;; Function signatures section.
          (when functions-list
            (with-section (section map "function_signatures")
              ;; Number of functions.
              (push (write-leb128-u32 (length functions-list) section) map)
              (dolist (fn wast)
                (when (and (consp fn) (eq (first fn) 'func))
                  ;; Function signature.
                  (let ((args (third fn))
                        (arg-types nil)
                        (results (fourth fn)))
                    (assert (<= (length results) 1))
                    (dolist (a args)
                      (push (second a) arg-types))
                    (let* ((signature `(,(first results) ,@(nreverse arg-types)))
                           (signum (position signature signatures :test 'equalp)))
                      (assert signum)
                      (push (write-leb128-u32 signum section) map)))))))
          ;;
          ;; Function Table section.
          (when function-table
            (with-section (section map "function_table")
              (push (write-leb128-u32 (length function-table) section) map)
              (dolist (fn function-table)
                (push (write-leb128-u32 (functions-index fn) section) map))))
          ;;
          ;; Write the memory section.
          (when memory-sections
            (assert (= (length memory-sections) 1))
            (with-section (section map "memory")
              (destructuring-bind (mem-min-pages &rest segments)
                  (first memory-sections)
                (let ((mem-max-pages mem-min-pages))
                  (when (integerp (first segments))
                    (setf mem-max-pages (pop segments)))
                  (push (write-leb128-u32 mem-min-pages section) map)
                  (push (write-leb128-u32 mem-max-pages section) map))
                ;; Memory export.
                (push (write-u8 (if export-memory-p 1 0) section) map)
                (setf data-segments segments))))
          ;;
          ;; Exports section
          (when exported-functions
            (with-section (section map "export_table")
              (push (write-leb128-u32 (length exported-functions) section) map)
              (dolist (export exported-functions)
                (destructuring-bind (internal-name . external-name)
                    export
                  (push (write-leb128-u32 (functions-index internal-name) section) map)
                  (push (write-wasm-string external-name section) map)))))
          ;;
          ;; Start function section.
          (when start-function
            (with-section (section map "start_function")
              (push (write-leb128-u32 (functions-index start-function) section) map)))
          ;;
          ;; Functions bodies section.
          (when functions-list
            (with-section (bodies fn-bodies-map "function_bodies")
              ;; Number of functions.
              (push (write-leb128-u32 (length functions-list) bodies) fn-bodies-map)
              ;;
              ;; Emit the functions.
              (dolist (fn wast)
                (when (and (consp fn) (eq (first fn) 'func))
                  (let* ((body-map nil)
                         (body-bytes (make-array '(0) :adjustable t :fill-pointer t
                                                :element-type '(unsigned-byte 8)))
                         ;; The signature.
                         (signature nil)
                         ;; Body.
                         (body (cddddr fn))
                         ;;
                         ;; Locals.
                         (vars nil)
                         (vars-groups nil)
                         ;;
                         (locals-map (compute-locals-map fn))
                         ;;
                         ;; Block targets.
                         (block-targets nil)
                         ;;
                         ;; Local variable indexes to emit at the end of the function.
                         (later-locals nil)
                         ;; u8 values to write at the end of the function.
                         (later-u8s nil)
                         (later-leb128-i32s nil)
                         (later-block-counts nil)
                         (later-br nil)
                         )
                    (when names-p
                      (push locals-map locals-names))
                    (when (eq (caar body) 'let)
                      (assert (not (cdr body)))
                      (setf vars (second (first body)))
                      (setf body (cddar body)))
                    ;; Group the local variables.
                    (let ((current-type nil)
                          (current-count 0))
                      (dolist (var vars)
                        (let ((type (second var)))
                          (unless (eq type current-type)
                            (when (plusp current-count)
                              (push (cons current-count current-type) vars-groups))
                            (setf current-type type)
                            (setf current-count 0))
                          (incf current-count)))
                      (when (plusp current-count)
                        (push (cons current-count current-type) vars-groups))
                      (setf vars-groups (nreverse vars-groups)))
                    ;;
                    ;; Local variables.
                    (push (write-leb128-u32 (length vars-groups) body-bytes) body-map)
                    (dolist (group vars-groups)
                      (destructuring-bind (count . type)
                          group
                        (push (write-leb128-u32 count body-bytes) body-map)
                        (push (write-u8 (wasm-type-code type) body-bytes) body-map)))
                    ;;
                    ;; Function signature.
                    (let ((args (third fn))
                          (arg-types nil)
                          (results (fourth fn)))
                      (assert (<= (length results) 1))
                      (dolist (a args)
                        (push (second a) arg-types))
                      (setf signature `(,(first results) ,@(nreverse arg-types))))
                    ;;
                    ;; Body.
                    (labels ((emit (list)
                               (let ((forms nil))
                                 (cond ((consp list)
                                        (let ((op (first list)))
                                          (case op
                                            (call
                                             (push (write-opcode 'call body-bytes) forms)
                                             (push (write-leb128-u32 (functions-index (second list)) body-bytes) forms)
                                             (dolist (el (cddr list))
                                               (push (emit el) forms)))
                                            (call_import
                                             (push (write-opcode 'call_import body-bytes) forms)
                                             (push (write-leb128-u32 (imports-index (second list)) body-bytes) forms)
                                             (dolist (el (cddr list))
                                               (push (emit el) forms)))
                                            (call_indirect
                                             (push (write-opcode 'call_indirect body-bytes) forms)
                                             (push (write-leb128-u32 (indirect-call-type (second list)) body-bytes) forms)
                                             (dolist (el (cddr list))
                                               (push (emit el) forms)))
                                            (block
                                                (let ((label (second list))
                                                      (size (- (length list) 2)))
                                                  (cond ((and (not label)
                                                              (= size 1))
                                                         ;; Skip the block in this case, for sexp-wasm compat.
                                                         (emit (third list)))
                                                        (t
                                                         (push (write-opcode op body-bytes) forms)
                                                         (assert (symbolp label))
                                                         (let ((size (- (length list) 2)))
                                                           (cond (t ; (inline-arg list)
                                                                  (push (write-leb128-u32 size body-bytes) forms))
                                                                 (t
                                                                  (push size later-block-counts))))
                                                         (push label block-targets)
                                                         (dolist (el (cddr list))
                                                           (push (emit el) forms))
                                                         (assert (eq (pop block-targets) label))
                                                         ))))
                                            ;;
                                            (loop
                                               (push (write-opcode op body-bytes) forms)
                                               (let ((label1 (second list))
                                                     (label2 (third list)))
                                                 (assert (symbolp label1))
                                                 (assert (symbolp label2))
                                                 (push (write-leb128-u32 (- (length list) 3) body-bytes) forms)
                                                 (push label1 block-targets)
                                                 (push label2 block-targets)
                                                 (dolist (el (cdddr list))
                                                   (push (emit el) forms))
                                                 (assert (eq (pop block-targets) label2))
                                                 (assert (eq (pop block-targets) label1))))
                                            (tableswitch
                                             (push (write-opcode op body-bytes) forms)
                                             (let* ((label (second list))
                                                    (key (third list))
                                                    (table (fourth list))
                                                    (table-length (+ (1- (length table)) 1))
                                                    (default (fifth list))
                                                    (cases nil))
                                               (assert (symbolp label))
                                               (assert (eq (first table) 'table))
                                               (dolist (c (cddr (cdddr list)))
                                                 (assert (eq (first c) 'case))
                                                 (push (second c) cases))
                                               (setf cases (nreverse cases))
                                               ;; num cases
                                               (push (write-u16 (length cases) body-bytes) forms)
                                               ;; num targets
                                               (push (write-u16 table-length body-bytes) forms)
                                               ;; The block is bound around the entire table, even the key expression.
                                               (push label block-targets)
                                               (flet ((emit-case-or-br (c)
                                                        (assert (endp (cddr c)))
                                                        (ecase (first c)
                                                          (case
                                                              (let* ((label (second c))
                                                                     (index (position label cases)))
                                                                (assert index)
                                                                ;; case index
                                                                (push (write-u16 index body-bytes) forms)))
                                                          (br
                                                           (let* ((label (second c))
                                                                  (depth (position label block-targets)))
                                                             (assert depth)
                                                             ;; High bit tagging to distinguish a break depth from a case index.
                                                             (push (write-u16 (logior depth #x8000) body-bytes) forms))))))
                                                 ;; Emit the jump table.
                                                 (dolist (c (rest table))
                                                   (emit-case-or-br c))
                                                 ;; The default index.
                                                 (emit-case-or-br default))
                                               ;; Emit the key expression.
                                               (push (emit key) forms)
                                               ;; Emit each of the case operands.
                                               (dolist (c (cddr (cdddr list)))
                                                 (cond ((= (length c) 2)
                                                        ;; Fall through, nop fill.
                                                        (push (emit '(nop)) forms))
                                                       ((= (length c) 3)
                                                        (let ((case-form (third c)))
                                                          (push (emit case-form) forms)))
                                                       (t
                                                        ;; Need a block.
                                                        (push (emit `(block nil ,@(cddr c))) forms))))
                                               (assert (eq (pop block-targets) label))))
                                            ;;
                                            (br_table
                                             (push (write-opcode op body-bytes) forms)
                                             (destructuring-bind (targets default key)
                                                 (rest list)
                                               (let ((num-targets (length targets)))
                                                 (push (write-leb128-u32 num-targets body-bytes) forms)
                                                 (dolist (label targets)
                                                   (let ((depth (position label block-targets)))
                                                     (assert depth)
                                                     (push (write-u32 depth body-bytes) forms))))
                                               (let ((depth (position default block-targets)))
                                                 (push (write-u32 depth body-bytes) forms))
                                               ;; Emit the key expression.
                                               (push (emit key) forms)))
                                            ;;
                                            (return
                                              (push (write-opcode op body-bytes) forms)
                                              ;; v8 determines the arity from the function signature.
                                              (cond ((first signature)
                                                     (assert (= (length list) 2))
                                                     (push (emit (second list)) forms))
                                                    (t
                                                     (assert (= (length list) 1)))))
                                            (otherwise
                                             (push (write-opcode op body-bytes) forms)
                                             (let ((info (gethash op opcode-table)))
                                               (unless info
                                                 (warn "Unexpected operator: ~S~%" op))
                                               (let* ((args (rest list))
                                                      (arg-types (third info))
                                                      (rest-type (fourth info)))
                                                 ;; V8 encoding fill; the branch value
                                                 ;; with a nop when unused.
                                                 (case op
                                                   (br
                                                    (when (endp (cddr list))
                                                      (setf args (list (first args) '(nop)))))
                                                   (br_if
                                                    (when (endp (cdddr list))
                                                      (setf args (list (first args) '(nop) (second args))))))
                                                 (when rest-type
                                                   (assert (member op '(block case loop call call_import
                                                                        call_indirect tableswitch when unless)))
                                                   (push (write-leb128-u32 (1- (length list)) body-bytes) forms))
                                                 ;; Read immediate arguments.
                                                 (do ()
                                                     ((or (endp arg-types) (endp args)))
                                                   (let ((type (pop arg-types))
                                                         (arg (first args)))
                                                     (cond ((member type '(i32 i64 f32 f64 p nil *))
                                                            (push (emit arg) forms)
                                                            (setf args (rest args)))
                                                           ((eq type 'branch)
                                                            (assert arg)
                                                            (let ((depth (position arg block-targets)))
                                                              (cond (depth
                                                                     (cond (t ;(inline-arg list)
                                                                            (push (write-leb128-u32 depth body-bytes) forms))
                                                                           (t
                                                                            (push depth later-br))))
                                                                    (t
                                                                     (warn "Branch target not found: ~S~%" arg)
                                                                     (push (write-leb128-u32 #xffff body-bytes) forms))))
                                                            (setf args (rest args)))
                                                           ((eq type 'local)
                                                            (let ((index (position arg locals-map)))
                                                              (unless index
                                                                (warn "Local variable ~S not found in ~S~%" arg locals-map))
                                                              (assert index)
                                                              (cond ((inline-arg list)
                                                                     (push (write-leb128-u32 index body-bytes) forms))
                                                                    (t
                                                                     (push index later-locals))))
                                                            (setf args (rest args)))
                                                           ((eq type 'i32-imm)
                                                            (let ((v (etypecase arg
                                                                       ((unsigned-byte 31)
                                                                        arg)
                                                                       ((unsigned-byte 32)
                                                                        (- #x100000000 arg))
                                                                       ((signed-byte 32)
                                                                        arg))))
                                                              (cond (t ; (inline-arg list)
                                                                     (push (write-leb128-i32 v body-bytes) forms))
                                                                    (t
                                                                     (push v later-leb128-i32s))))
                                                            (setf args (rest args)))
                                                           ((eq type 'i64-imm)
                                                            (let ((v (etypecase arg
                                                                       ((unsigned-byte 63)
                                                                        arg)
                                                                       ((unsigned-byte 64)
                                                                        (- #x10000000000000000 arg))
                                                                       ((signed-byte 64)
                                                                        arg))))
                                                              (push (write-leb128-i64 v body-bytes) forms)
                                                              (setf args (rest args))))
                                                           ((eq type 'f32-imm)
                                                            (push (write-f32 arg body-bytes) forms)
                                                            (setf args (rest args)))
                                                           ((eq type 'f64-imm)
                                                            (push (write-f64 arg body-bytes) forms)
                                                            (setf args (rest args)))
                                                           ((and (consp type) (eq (first type) 'mem))
                                                            (let* ((natural-align (second type))
                                                                   (offset 0)
                                                                   (align natural-align))
                                                              (when (eq arg :offset)
                                                                (pop args)
                                                                (setf offset (pop args))
                                                                (assert (integerp offset))
                                                                (setf arg (first args)))
                                                              (when (eq arg :align)
                                                                (pop args)
                                                                (setf align (pop args))
                                                                (assert (integerp align)))
                                                              ;; Memory access byte and offset.
                                                              #+nil
                                                              (progn
                                                                ;; Original, old version
                                                                (let ((byte (logior (if (eql offset 0) 0 #x10)
                                                                                    (if (>= align natural-align) 0 #x80))))
                                                                  (push (write-u8 byte body-bytes) forms))
                                                                (unless (eql offset 0)
                                                                  (push (write-leb128-u32 offset body-bytes) forms)))
                                                              ;; Current variations.
                                                              ;;#+nil
                                                              (let ((align-log2 (round (log align 2))))
                                                                (push (write-leb128-u32 align-log2 body-bytes) forms))
                                                              #+nil
                                                              (cond ((>= align natural-align)
                                                                     (push (write-leb128-u32 0 body-bytes) forms))
                                                                    (t
                                                                     (let ((align-log2 (round (log align 2))))
                                                                       (push (write-leb128-u32 (1+ align-log2) body-bytes) forms))))
                                                              (push (write-leb128-u32 offset body-bytes) forms)
                                                              ))
                                                           (t
                                                            (error "Unexpected fixed argument type: ~S" type)))))
                                                 (when arg-types
                                                   (error "Missing arguments in form: ~S~%" list))
                                                 (when args
                                                   (error "Unexpected arguments in form: ~S~%" list))
                                                 (when rest-type
                                                   (loop
                                                      (assert args)
                                                      (let ((arg (pop args)))
                                                        (push (emit arg) forms))))))))
                                          ))
                                       ;; Leaf symbols and number here are inline immediates.
                                       ((symbolp list)
                                        (let ((index (assoc list locals-map)))
                                          (unless index
                                            (warn "Local variable ~S not found in ~S~%" list locals-map))
                                          (assert index)
                                          (push (write-leb128-u32 (cdr index) body-bytes) forms)))
                                       ((integerp list)
                                        (push (write-leb128-i64 list body-bytes) forms))
                                       (t
                                        (warn "Unexpected: ~S~%" list)))
                                 (nreverse forms))))
                      ;;
                      (dolist (form body)
                        (push (emit form) body-map))
                      (dolist (local later-locals)
                        (push (write-leb128-u32 local body-bytes) body-map))
                      (dolist (u8 later-u8s)
                        (push (write-u8 u8 body-bytes) body-map))
                      (dolist (i32 later-leb128-i32s)
                        (push (write-leb128-i32 i32 body-bytes) body-map))
                      (dolist (u8 later-block-counts)
                        (push (write-u8 u8 body-bytes) body-map))
                      (dolist (u8 later-br)
                        (push (write-u8 u8 body-bytes) body-map))
                      )
                    (let ((size (write-leb128-u32 (length body-bytes) bodies)))
                      (dotimes (i (length body-bytes))
                        (vector-push-extend (aref body-bytes i) bodies))
                      (push `((:body ,(length body-bytes))
                              ,size
                              ,@(nreverse body-map))
                            fn-bodies-map)))
                  ))))
          ;;
          ;; Segments are in a data segments section.
          (when data-segments
            (assert memory-sections)
            (with-section (section map "data_segments")
              (push (write-leb128-u32 (length data-segments) section) map)
              (dolist (segment data-segments)
                (destructuring-bind (start (&rest data))
                    (rest segment)
                  (push (write-leb128-u32 start section) map)
                  (push (write-leb128-u32 (length data) section) map)
                  (dolist (byte data)
                    (push (write-u8 byte section) map))))))

          ;; Names section.
          (when names-p
            (setf locals-names (nreverse locals-names))
            (with-section (section map "names")
              (push (write-leb128-u32 (length functions-list) section) map)
              (do ((function-names functions-list (rest function-names))
                   (locals-names locals-names (rest locals-names)))
                  ((endp function-names))
                (let* ((name (first function-names))
                       (name-string (maybe-invert-label (symbol-name name))))
                  (push (write-wasm-string name-string section) map))
                (let ((locals (first locals-names)))
                  (push (write-leb128-u32 (length locals) section) map)
                  (dolist (local locals)
                    (let ((name-string (maybe-invert-label (symbol-name local))))
                      (push (write-wasm-string name-string section) map)))))))
          ;;
          ;; Sections End
          ;;(with-section (section map "end"))
          ;;
          (setf *wasm-source-map* (nreverse sections))
          ;;
          module-bytes)))))

(defun write-wasm-to-file (wast &key (file "/tmp/test.wasm")
                                  (reorder-opcodes nil) (inline t) (names-p t))
  "Write the 'wast to a wasm encoded binary file."
  (let ((bytes (write-wasm wast :reorder-opcodes reorder-opcodes
                           :inline inline :names-p names-p)))
    (with-open-file (stream file :direction :output
                            :element-type '(unsigned-byte 8)
                            :if-exists :supersede)
      (dotimes (i (length bytes))
        (write-byte (aref bytes i) stream))))
  nil)

#|

;;; Example:
(defvar *module1*)
(setf *module1* (import-wast-from-file "test.wast"))
(show-wast-opcode-counts *module1*)
(write-wasm-to-file *module1* :file "/tmp/test.wasm")

|#


;;;; Read and decoding a wasm binary file.

(defun maybe-invert-label (string)
  "Invert the 'string label on CL implementations with standard uppercase
  symbol names. Following the standard CL rules so the case can be preserved
  by printing with inverted case. Returns a new string if it changes."
  #+scl
  (when (eq ext:*case-mode* :lower)
    (return-from maybe-invert-label string))
  (let ((all-lower t)
        (all-upper t)
        (length (length string)))
    (dotimes (i length)
      (let ((ch (aref string i)))
        (when (both-case-p ch)
          (if (upper-case-p ch)
              (setf all-lower nil)
              (setf all-upper nil)))))
    (cond (all-lower
           (let ((new (make-string length)))
             (dotimes (i length)
               (setf (aref new i) (char-upcase (aref string i))))
             new))
          (all-upper
           (let ((new (make-string length)))
             (dotimes (i length)
               (setf (aref new i) (char-downcase (aref string i))))
             new))
          (t 
           string))))


(defun decode-wasm (file)
  "Decode a wasm binary file into a canonical text source code encoding."
  (let (;; Table mapping the opcode index to the opcode info.
        (opcode-table (make-hash-table))
        ;;
        ;; The module form.
        (module (list 'module))
        ;; Memory section.
        (memory-section nil)
        ;; Signatures section.
        (signatures nil)
        ;; Function signatures section.
        (function-signatures nil)
        ;; Signature labels used by call-direct.
        (call-direct-signatures nil)
        ;;
        ;; Functions sections.
        (functions nil)
        ;; The exports and imports lists.
        (exports nil)
        (imports nil)
        ;;
        ;; Function table section.
        (function-tables nil)
        ;;
        ;; The optional start function section.
        (start-function nil)
        ;;
        (names-section nil)
        ;;
        ;; Web Low-level Language section.
        (wll-section-size 0)
        (wll-section-position nil)
        ;;
        (found-section-end-p nil)
        )
    (dolist (info (reverse *wasm-opcodes*))
      (setf (gethash (second info) opcode-table) info))
    (labels ((read-u8 (stream)
               (read-byte stream))
             (read-i8 (stream)
               (let ((u (read-byte stream)))
                 (if (>= u 128) (- u 256) u)))
             (read-u16 (stream)
               (logior (read-byte stream) (ash (read-byte stream) 8)))
             (read-u32 (stream)
               (logior (read-byte stream)
                       (ash (read-byte stream) 8)
                       (ash (read-byte stream) 16)
                       (ash (read-byte stream) 24)))
             (read-s32 (stream)
               (let ((u (read-u32 stream)))
                 (if (>= u #x80000000) (- u #x100000000) u)))
             (read-f64 (stream)
               (let ((low (read-u32 stream))
                     (high (read-s32 stream)))
                 (make-wast-double-float :bits (logior (ash high 32) low))))
             (read-f32 (stream)
               (let ((bits (read-s32 stream)))
                 (make-wast-single-float :bits bits)))
             (read-leb128-u32 (stream)
               (let ((v 0)
                     (shift 0))
                 (dotimes (i 5 (error "LEB128 u32 too long"))
                   (let ((b (read-byte stream)))
                     (setf v (logior (ash (logand b #x7f) shift) v))
                     (incf shift 7)
                     (unless (logbitp 7 b)
                       (assert (typep v '(unsigned-byte 32)))
                       (return v))))))
             (read-leb128-u32-or-nil (stream)
               ;; As for read-leb128-u32 but handles an EOF return 'nil.
               (let ((v 0)
                     (shift 0))
                 (let ((b (read-byte stream nil nil)))
                   (unless b
                     (return-from read-leb128-u32-or-nil nil))
                   (setf v (logior (ash (logand b #x7f) shift) v))
                   (incf shift 7)
                   (unless (logbitp 7 b)
                     (assert (typep v '(unsigned-byte 32)))
                     (return-from read-leb128-u32-or-nil v)))
                 (dotimes (i 4 (error "LEB128 u32 too long"))
                   (let ((b (read-byte stream)))
                     (setf v (logior (ash (logand b #x7f) shift) v))
                     (incf shift 7)
                     (unless (logbitp 7 b)
                       (assert (typep v '(unsigned-byte 32)))
                       (return v))))))
             (read-leb128-i32 (stream)
               (let ((v 0)
                     (shift 0))
                 (dotimes (i 5 (error "LEB128 i32 too long"))
                   (let ((b (read-byte stream)))
                     (setf v (logior (ash (logand b #x7f) shift) v))
                     (incf shift 7)
                     (unless (logbitp 7 b)
                       (return (cond ((logbitp 6 b)
                                      (let ((vs (- v (ash 1 shift))))
                                        (assert (typep vs '(signed-byte 32)))
                                        vs))
                                     (t
                                      (assert (typep v '(unsigned-byte 31)))
                                      v))))))))
             #+nil ; not yet used
             (read-leb128-u64 (stream)
               (let ((v 0)
                     (shift 0))
                 (dotimes (i 10 (error "LEB128 u64 too long"))
                   (let ((b (read-byte stream)))
                     (setf v (logior (ash (logand b #x7f) shift) v))
                     (incf shift 7)
                     (unless (logbitp 7 b)
                       (assert (typep v '(unsigned-byte 64)))
                       (return v))))))
             (read-leb128-i64 (stream)
               (let ((v 0)
                     (shift 0))
                 (dotimes (i 10 (error "LEB128 i64 too long"))
                   (let ((b (read-byte stream)))
                     (setf v (logior (ash (logand b #x7f) shift) v))
                     (incf shift 7)
                     (unless (logbitp 7 b)
                       (return (cond ((logbitp 6 b)
                                      (let ((vs (- v (ash 1 shift))))
                                        (assert (typep vs '(signed-byte 64)))
                                        vs))
                                     (t
                                      (assert (typep v '(unsigned-byte 63)))
                                      v))))))))
             (type-from-code (code)
               (ecase code
                 (0 nil)
                 (1 'i32)
                 (2 'i64)
                 (3 'f32)
                 (4 'f64)))
             (type-prefix (type)
               (ecase type
                 (i32 '#:i)
                 (i64 '#:j)
                 (f32 '#:f)
                 (f64 '#:d)))
             (read-signature (stream)
               (let ((param-count (read-leb128-u32 stream))
                     (return-type (type-from-code (read-u8 stream)))
                     (param-types nil))
                 (dotimes (i param-count)
                   (push (type-from-code (read-u8 stream)) param-types))
                 (when return-type
                   (setf return-type (list return-type)))
                 `(func ,(nreverse param-types) ,return-type)))
             (next-signature-name ()
               (intern (format nil "~A~d" '#:$sig (length signatures)) :cl-user))
             (read-wasm-string (stream)
               (let ((len (read-leb128-u32 stream)))
                 ;; todo utf-8
                 (with-output-to-string (s)
                   (dotimes (i len)
                     (write-char (code-char (read-byte stream)) s)))))
             )
      (with-open-file (stream file :direction :input
			      :element-type '(unsigned-byte 8))
        ;; Check the magic number
        (let ((magic (read-u32 stream)))
          (assert (= magic #x6d736100)))
        (let ((version (read-u32 stream)))
          (assert (= version 10)))
        (loop
           (let ((section-size (read-leb128-u32-or-nil stream)))
             (unless section-size
               (return))
             (let ((section-start (file-position stream))
                   (section-name (read-wasm-string stream)))
               (cond ((string= section-name "memory")
                      ;; Expect only one memory section.
                      (assert (not memory-section))
                      (multiple-value-bind (mem-min-pages mem-max-pages)
                          (values (read-leb128-u32 stream)
                                  (read-leb128-u32 stream))
                        (setf memory-section (list 'memory mem-min-pages mem-max-pages))
                        (push memory-section module)
                        (let ((memory-export-p (/= (read-u8 stream) 0)))
                          (when memory-export-p
                            (push `(export memory "memory") module)))
                        ))
                     ((string= section-name "signatures")
                      (let ((sigs nil))
                        (dotimes (i (read-leb128-u32 stream))
                          (push (read-signature stream) sigs))
                        (setf sigs (nreverse sigs))
                        (dolist (sig sigs)
                          (let ((name-type (list (next-signature-name) sig)))
                            (push `(type ,@name-type) module)
                            (push name-type signatures))))
                      (setf signatures (nreverse signatures)))
                     ((string= section-name "import_table")
                      (dotimes (i (read-leb128-u32 stream))
                        (let* ((signature-index (read-leb128-u32 stream))
                               (module-name (read-wasm-string stream))
                               (function-name (read-wasm-string stream))
                               ;; Attach the import index to the constructed
                               ;; name as they can be repeated with the same
                               ;; names and signature.
                               (label (intern (format nil "$~A~D"
                                                      (maybe-invert-label function-name)
                                                      (length imports))
                                              :cl-user))
                               (def (list 'import label module-name function-name (list 'type signature-index))))
                          (push def imports)
                          (push def module)))
                      (setf imports (nreverse imports)))
                     ((string= section-name "function_signatures")
                      ;; The function bodies are not read on the first pass - wait
                      ;; until enough information is available to complete them
                      ;; one at a time to keep the peak memory usage down.
                      (dotimes (i (read-leb128-u32 stream))
                        (push (read-leb128-u32 stream) function-signatures))
                      (setf function-signatures (nreverse function-signatures)))
                     ((string= section-name "function_bodies")
                      ;; The function bodies are not read on the first pass - wait
                      ;; until enough information is available to complete them
                      ;; one at a time to keep the peak memory usage down.
                      (let ((num-bodies (read-leb128-u32 stream)))
                        (dotimes (i num-bodies)
                          (let ((body-position nil)
                                (body-bytes 0))
                            (setf body-bytes (read-leb128-u32 stream))
                            (setf body-position (file-position stream))
                            ;; Skip the body for now.
                            (dotimes (i body-bytes)
                              (read-byte stream))
                            ;; Function definition. Expect a body.
                            (assert body-bytes)
                            (let ((def (list 'func (length functions)
                                             (list 'type (elt function-signatures i))
                                             (list body-position body-bytes))))
                              (push def module)
                              (push def functions)))))
                      (setf functions (nreverse functions)))
                     ((string= section-name "export_table")
                      (dotimes (i (read-leb128-u32 stream))
                        (let* ((function-index (read-leb128-u32 stream))
                               (export-name (read-wasm-string stream))
                               (def (list 'export 'func export-name function-index)))
                          (push def exports)
                          (push def module)))
                      (setf exports (nreverse exports)))
                     ((string= section-name "data_segments")
                      (let ((memory-segments nil))
                        (dotimes (i (read-leb128-u32 stream))
                          (let ((dest-addr (read-leb128-u32 stream))
                                (data nil))
                            (dotimes (i (read-leb128-u32 stream))
                              (push (read-byte stream) data))
                            (push (list 'segment dest-addr (nreverse data)) memory-segments)))
                        (when memory-segments
                          (assert memory-section)
                          (setf (rest (last memory-section)) (nreverse memory-segments)))))
                     ((string= section-name "start_function")
                      (when start-function
                        (warn "Module start function already declared"))
                      (let* ((index (read-leb128-u32 stream))
                             (def `(start ,index)))
                        (setf start-function def)
                        (push def module)))
                     ((string= section-name "function_table")
                      (let ((table nil))
                        (dotimes (i (read-leb128-u32 stream))
                          (let ((function-index (read-leb128-u32 stream)))
                            (push function-index table)))
                        (when table
                          (let ((def `(table ,@(nreverse table))))
                            (push def function-tables)
                            (push def module)))))
                     ((string= section-name "end")
                      (setf found-section-end-p t))
                     ((string= section-name "names")
                      (dotimes (i (read-leb128-u32 stream))
                        (let ((fn-name (intern (read-wasm-string stream) :cl-user))
                              (num-locals (read-leb128-u32 stream))
                              (local-names nil))
                          (dotimes (j num-locals)
                            (push (intern (read-wasm-string stream) :cl-user) local-names))
                          (push (list fn-name (nreverse local-names)) names-section)))
                      (setf names-section (nreverse names-section)))
                     (t
                      ;; Skip on this pass, for now anyway.
                      (dotimes (i (- section-size (- (file-position stream) section-start)))
                        (read-u8 stream)))
                     )                  ; cond
               (assert (= (+ section-start section-size) (file-position stream)))
               )
             )
           ) ; loop
        ;;
        (setf function-tables (nreverse function-tables))
        (setf module (nreverse module))
        ;;
        ;; Name the functions.
        (dolist (func functions)
          (let* ((index (second func))
                 (name (and (< index (length names-section))
                            (first (elt names-section index)))))
            (unless name
              (setf name (intern (format nil "~A~D" '#:$f index) :cl-user))
              (assert (not (member name names-section))))
            (setf (second func) name)))
        ;;
        ;; Label the exports. There can be multiple exports per
        ;; function, so a name can not in general be defined from the
        ;; export name, so use the first.
        (let ((export-function-indexes nil))
          (dolist (export exports)
            (assert (eq (second export) 'func))
            (let ((function-index (fourth export)))
              (cond ((member function-index export-function-indexes)
                     ;; Copy the prior function name.
                     (let* ((function (elt functions function-index))
                            (function-name (second function)))
                       (setf (fourth export) function-name)))
                    (t
                     (push function-index export-function-indexes)
                     (let ((name (and (< function-index (length names-section))
                                      (first (elt names-section function-index)))))
                       (cond (name
                              ;; Already named, use it.
                              (setf (fourth export) name))
                             (t
                              ;; Create a name based on the export.
                              (let* ((export-name (third export))
                                     (export-label (intern (format nil "$~A" (maybe-invert-label export-name))
                                                           :cl-user))
                                     (function (elt functions function-index)))
                                ;; Check for a conflict with other names.
                                (dolist (func functions)
                                  (assert (not (eq export-label (second func)))))
                                (setf (second function) export-label)
                                (setf (fourth export) export-label))))))))))

        ;; Map the function table function indexes to the function names.
        (dolist (table function-tables)
          (do ((table (rest table) (rest table)))
              ((endp table))
            (setf (first table) (second (elt functions (first table))))))

        ;; Map the start function index to the function name.
        (when start-function
          (setf (second start-function) (second (elt functions (second start-function)))))

        ;; Map the import and function types to their labels
        (dolist (import imports)
          (assert (eq (first import) 'import))
          (let* ((type (first (last import)))
                 (index (second type)))
            (assert (<= index (length signatures)))
            (setf (second type) (first (elt signatures index)))))
        (dolist (func functions)
          (assert (eq (first func) 'func))
          (let* ((type (third func))
                 (index (second type)))
            (assert (<= index (length signatures)))
            (setf (second type) (first (elt signatures index)))))

        (do ((funcs functions (rest funcs))
             (func-index 0 (1+ func-index)))
            ((endp funcs))
          ;; Assigned names to function the arguments and locals.
          (let* ((func (first funcs))
                 (name (second func))
                 ;;
                 (signature-name (second (third func)))
                 (signature (assoc signature-name signatures))
                 (signature-type (second signature))
                 ;;
                 ;; List of arguments with labels and types.
                 (arguments nil)
                 ;; List of result types.
                 (results nil)
                 ;;
                 ;; Names for arguments and local variables.
                 (local-names (second (assoc name names-section)))
                 ;;
                 (next-local 0)
                 ;; The local variables 'let definition list.
                 (locals-let nil)
                 ;; List mapping param/local index to their symbol.
                 (locals-list nil)
                 ;;
                 (forms nil)
                 ;;
                 ;; Counter for default block and loop labels.
                 (next-label 0)
                 ;; Label binding stack.
                 (label-bindings nil)
                 ;;
                 ;; Debug.
                 (nesting 0)
                 )
            (assert (eq (first func) 'func))
            ;; Start with the arguments.
            (let ((arg-types (first (rest signature-type))))
              (dolist (type arg-types)
                (let* ((name (or (and local-names
                                      (or (< next-local (length local-names))
                                          (error "Insufficient named locals in function ~S: ~D ~S" name next-local local-names))
                                      (elt local-names next-local))
                                 (let ((prefix (type-prefix type)))
                                   (intern (format nil "$~A~d" prefix next-local) :cl-user))))
                       (def `(,name ,type)))
                  (push def arguments)
                  (push name locals-list))
                (incf next-local))
              (setf arguments (nreverse arguments)))
            (setf results (second (rest signature-type)))
            ;;
            ;; Process the function body.
            (destructuring-bind (body-position body-size)
                (first (last func))
              (assert body-position)
              (assert (file-position stream body-position))
              ;;
              ;; Local variables.
              (dotimes (i (read-leb128-u32 stream))
                (let ((count (read-leb128-u32 stream))
                      (type (type-from-code (read-u8 stream))))
                  (dotimes (j count)
                    (let ((name (or (and local-names
                                      (or (< next-local (length local-names))
                                          (error "Insufficient named locals in function ~S: ~D ~S~%~S" name next-local local-names locals-list))
                                      (elt local-names next-local))
                                    (let* ((prefix (ecase type
                                                     (i32 '#:$i)
                                                     (i64 '#:$j)
                                                     (f32 '#:$f)
                                                     (f64 '#:$d))))
                                      (intern (format nil "~A~d" prefix next-local) :cl-user)))))
                      (push (list name type) locals-let)
                      (push name locals-list))
                    (incf next-local))))
              (setf locals-list (nreverse locals-list))
              (setf locals-let (nreverse locals-let))
              ;;
              (labels ((next-block-label ()
                         (let ((label (intern (format nil "~A~D" '#:$block- next-label) :cl-user)))
                           (incf next-label)
                           label))
                       (next-switch-label ()
                         (let ((label (intern (format nil "~A~D" '#:$switch- next-label) :cl-user)))
                           (incf next-label)
                           label))
                       (next-loop-labels ()
                         (let ((label (intern (format nil "~A~D" '#:$loop- next-label) :cl-user))
                               (repeat (intern (format nil "~A~D" '#:$repeat- next-label) :cl-user)))
                           (incf next-label)
                           (values label repeat)))
                       (read-exp ()
                         (incf nesting)
                         (let ((size (- (file-position stream) body-position)))
                           (when (> size body-size)
                             (error "Function body read overflow in: ~S~%" (second func))))
                         (let* ((opcode (read-byte stream))
                                (info (gethash opcode opcode-table))
                                (name (first info))
                                (form `(,name)))
                           (unless info
                             (error "Unrecognized opcode: ~X" opcode))
                           ;; Special handling for call, call_import, and call_indirect.
                           (case name
                             (call
                              (let* ((functions-index (read-leb128-u32 stream))
                                     (function (elt functions functions-index))
                                     (type (third function))
                                     (signature (assoc (second type) signatures)))
                                (assert (eq (first function) 'func))
                                (assert signature)
                                (push (second function) form)
                                (dotimes (i (length (second (second signature))))
                                  (push (read-exp) form))))
                             (call_import
                              (let* ((imports-index (read-leb128-u32 stream))
                                     (import (elt imports imports-index))
                                     (type (first (last import)))
                                     (signature (assoc (second type) signatures)))
                                (assert (eq (first import) 'import))
                                (assert signature)
                                (push (second import) form)
                                (dotimes (i (length (second (second signature))))
                                  (push (read-exp) form))))
                             (call_indirect
                              (let* ((index (read-leb128-u32 stream))
                                     (signature (elt signatures index))
                                     (label (first signature))
                                     (type (second signature)))
                                (push label form)
                                ;; Expression giving the index into the function table.
                                (push (read-exp) form)
                                (dotimes (i (length (second type)))
                                  (push (read-exp) form))
                                ;; Note signatures used by call_direct.
                                (pushnew label call-direct-signatures)))
                             (tableswitch
                              (break)
                              (let ((switch-label (next-switch-label)))
                                (push switch-label form)
                                ;; The switch label is bound for all forms.
                                (push switch-label label-bindings)
                                (let ((num-cases (read-u16 stream))
                                      (table-length (read-u16 stream)))
                                  (labels ((case-label (n)
                                             (intern (format nil "~A~D" '#:$switch-case$ n)))
                                           (read-case ()
                                             (let ((n (read-u16 stream)))
                                               ;; Bit 15 flags a 'br versus a 'case.
                                               (cond ((logbitp 15 n)
                                                      `(br ,(elt label-bindings (ldb (byte 15 0) n))))
                                                     (t
                                                      (assert (< n num-cases))
                                                      `(case ,(case-label n)))))))
                                    (let ((table nil))
                                      (dotimes (i (1- table-length))
                                        (push (read-case) table))
                                      (let ((default-case (read-case)))
                                        ;; The key expression.
                                        (push (read-exp) form)
                                        (push `(table ,@(nreverse table)) form)
                                        ;; Default case.
                                        (push default-case form)))
                                    (dotimes (i num-cases)
                                      (push `(case ,(case-label i) ,(read-exp)) form))))
                                (assert (eq (pop label-bindings) switch-label))))
                             (br_table
                              (let ((num-targets (read-leb128-u32 stream))
                                    (targets nil))
                                (dotimes (i num-targets)
                                  (let ((depth (read-u32 stream)))
                                    (push (elt label-bindings depth) targets)))
                                (push (nreverse targets) form)
                                (let ((default-target (read-u32 stream)))
                                  (push (elt label-bindings default-target) form))
                                (let ((key (read-exp)))
                                  (push key form))))
                             (block
                                 (let ((label (next-block-label))
                                       (len (read-leb128-u32 stream)))
                                   (assert (equalp (fourth info) 'p))
                                   (push label form)
                                   (push label label-bindings)
                                   (dotimes (i len)
                                     (push (read-exp) form))
                                   (assert (eq (pop label-bindings) label))))
                             (loop
                                (multiple-value-bind (label repeat)
                                    (next-loop-labels)
                                  (assert (equalp (fourth info) 'p))
                                  (push label form)
                                  (push label label-bindings)
                                  (push repeat form)
                                  (push repeat label-bindings)
                                  (let ((len (read-leb128-u32 stream)))
                                    (dotimes (i len)
                                      (push (read-exp) form)))
                                  (assert (eq (pop label-bindings) repeat))
                                  (assert (eq (pop label-bindings) label))
                                  ))
                             (return
                               ;; v8 determines the arity from the function signature.
                               (when results
                                 (push (read-exp) form)))
                             (otherwise
                              (let* ((rest-type (fourth info))
                                     ;; Is the length also before immediates??
                                     (rest-len (if rest-type (read-leb128-u32 stream) 0)))
                                ;; Read immediate arguments.
                                (dolist (type (third info))
                                  (cond ((member type '(i32 i64 f32 f64 p nil *))
                                         (push (read-exp) form))
                                        ((eq type 'branch)
                                         (let* ((d (read-leb128-u32 stream))
                                                (label (elt label-bindings d)))
                                           (push label form)))
                                        ((eq type 'local)
                                         (let ((i (read-leb128-u32 stream)))
                                           (cond ((>= i (length locals-list))
                                                  (warn "Error: local variable index out or range: ~D~%" i)
                                                  (push 0 form))
                                                 (t
                                                  (let ((name (elt locals-list i)))
                                                    (push name form))))))
                                        ((eq type 'u8-imm)
                                         (push (read-u8 stream) form))
                                        ((eq type 'i32-imm)
                                         (push (read-leb128-i32 stream) form))
                                        ((eq type 'i64-imm)
                                         (push (read-leb128-i64 stream) form))
                                        ((eq type 'f32-imm)
                                         (push (read-f32 stream) form))
                                        ((eq type 'f64-imm)
                                         (push (read-f64 stream) form))
                                        ((and (consp type) (eq (first type) 'mem))
                                         (let ((natural-align (second type))
                                               (align (expt 2 (read-leb128-u32 stream)))
                                               (offset (read-leb128-u32 stream)))
                                           (unless (zerop offset)
                                             (push :offset form)
                                             (push offset form))
                                           (unless (= align natural-align)
                                             (push :align form)
                                             (push align form))))
                                        (t
                                         (error "Unexpected fixed argument type: ~S" type))))
                                (dotimes (i rest-len)
                                  (push (read-exp) form)))))
                           (setf form (nreverse form))
                           ;; Fixups to convert back from v8 to wast etc.
                           (case (first form)
                             (br
                              ;; Strip a nop, should be ok but sexpr-wasm complains.
                              (when (equalp (third form) '(nop))
                                (setf (cddr form) nil)))
                             (br_if
                              ;; Strip a nop, should be ok but sexpr-wasm complains.
                              (when (equalp (third form) '(nop))
                                (setf (rest form) (list (second form) (fourth form))))))
                           (decf nesting)
                           form)))
                (loop
                   (let ((size (- (file-position stream) body-position)))
                     (when (>= size body-size)
                       (return)))
                   (push (read-exp) forms))
                )
              (setf forms (nreverse forms))
              (setf (cdddr func) `(,arguments ,results
                                              ,@(if locals-let
                                                    `((let ,locals-let ,@forms))
                                                    forms)))
              )))

        ) ; with-open-file

      ;; Finished reading from the file.
      ;; Post-processing.

      ;; Note any signatures that are duplicates.
      (let ((duplicate-signatures nil))
        (dolist (signature signatures)
          (let ((name (first signature))
                (type (second signature)))
            (dolist (sig signatures)
              (unless (eq sig signature)
                (when (equalp type (second sig))
                  (push name duplicate-signatures))))))
        (when duplicate-signatures
          (warn "Found duplicate signatures: ~S~%" duplicate-signatures))
        (dolist (import imports)
          (assert (eq (first import) 'import))
          ;; Replace the import signatures by their param and results
          ;; lists unless they are duplicates.
          (let* ((type (fifth import))
                 (name (second type)))
            (unless (member name duplicate-signatures)
              (let ((signature (assoc name signatures)))
                (setf (cddddr import) (rest (second signature)))))))
        (dolist (function functions)
          (assert (eq (first function) 'func))
          ;; Remove signatures included with the functions unless they are
          ;; duplicates.
          (let* ((type (third function))
                 (name (second type)))
            (unless (member name duplicate-signatures)
              (setf (cddr function) (cdddr function)))))
        ;; Remove signature definitions from the module that are not used by
        ;; indirect calls and are not duplicates.
        (do ((module module))
            ((endp (rest module)))
          (let ((next (first (rest module))))
            (cond ((and (eq (first next) 'type)
                        (let ((name (second next)))
                          (and (not (member name duplicate-signatures))
                               (not (member name call-direct-signatures)))))
                   (setf (rest module) (rest (rest module))))
                  (t
                   (setf module (rest module))))))
        )
      )
    module
    ))

#|

Examples:

(export-wast-to-file (decode-wasm "/tmp/text.wasm") "/tmp/test.wast")

|#


