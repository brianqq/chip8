(declaim (optimize (debug 3) (safety 3)))
(deftype chipbyte () '(unsigned-byte 8))
(defun make-byte-array (size &rest extras)
  (apply #'make-array size :element-type 'chipbyte :adjustable nil extras))
(declaim (inline make-byte-array))

;; 0x000-0x1FF - Chip 8 interpreter (contains font set in emu)
;; 0x050-0x0A0 - Used for the built in 4x5 pixel font set (0-F)
;; 0x200-0xFFF - Program ROM and work RAM
(defconstant +startram+ #x200)
(defparameter *memory*
  (make-byte-array 4096))
(defparameter *registers*
  (make-byte-array 16))
(defparameter *index* 0)
(defparameter *pc* +startram+) 			;program counter
(defparameter *gfx*
  (make-byte-array '(64 32)))
(defparameter *gfx-flat*
  (make-byte-array (* 64 32) :displaced-to *gfx*))
(defparameter *delay-timer* 0)
(defparameter *sound-timer* 0)
(defparameter *stack*
  (make-byte-array 16))
(defparameter *sp* 0)
(defparameter *key*
  (make-byte-array 16))
(defparameter *max-val* #xFF)

(defun fetch-opcode ()
  (the unsigned-byte
   (logior (ash (aref *memory* *pc*) 8)
	   (aref *memory* (1+ *pc*)))))

(defun read-file (file)
  (with-open-file (stream file :element-type 'chipbyte)
    (read-sequence *memory* stream :start +startram+)))

(define-symbol-macro VX (aref *registers* X))
(define-symbol-macro VY (aref *registers* Y))
(define-symbol-macro VF (aref *registers* #xF))
(define-symbol-macro V0 (aref *registers* 0))
(define-symbol-macro stacktop (aref *stack* *sp*))
(defun next () (incf *pc* 2))
(declaim (inline next))

;; (defmacro ssetf (arg value)
;;   `(symbol-macrolet ((it ,arg))
;;      (setf it ,value)))

;;; run away it's the opcode table thing
(defparameter *opcodes*
  (loop for (opcode docstring . body) in 
       '(("0NNN" 	"Calls RCA 1802 program at address NNN.")
	 ("00E0" 	"Clears the screen."
	  (nsubstitute-if 0 (lambda (x) (declare (ignore x)) t) *gfx-flat*)) ;is there a more idiomatic way of doing this?
	 ("00EE" 	"Returns from a subroutine."
	  (decf stacktop)
	  (setf *pc* stacktop))
	 ("1NNN" 	"Jumps to address NNN."
	  holdpc
	  (setf *pc* N))
	 ("2NNN" 	"Calls subroutine at NNN."
	  holdpc
	  (setf stacktop *pc*)
	  (incf *sp*)
	  (setf *pc* N))
	 ("3XNN" 	"Skips the next instruction if VX equals NN."
	  (if (= VX N) (next)))
	 ("4XNN" 	"Skips the next instruction if VX doesn't equal NN."
	  (if (/= VX N) (next)))
	 ("5XY0" 	"Skips the next instruction if VX equals VY."
	  (if (= VX VY) (next)))
	 ("6XNN" 	"Sets VX to NN."
	  (setf VX N))
	 ("7XNN" 	"Adds NN to VX."
	  (incf VX N)) 			;overflow?
	 ("8XY0" 	"Sets VX to the value of VY."
	  (setf VX VY))
	 ("8XY1" 	"Sets VX to VX or VY."
	  (setf VX (logior VX VY)))
	 ("8XY2" 	"Sets VX to VX and VY."
	  (setf VX (logand VX VY)))
	 ("8XY3" 	"Sets VX to VX xor VY."
	  (setf VX (logxor VX VY)))
	 ("8XY4" 	"Adds VY to VX. VF is set to 1 when there's a carry, and to 0 when there isn't."
	  (let ((sum (+ VY VX)))
	    (setf VX (mod (+ VY VX) *max-val*)
		  VF (if (> sum *max-val*) 1 0))))
	 ("8XY5" 	"VY is subtracted from VX. VF is set to 0 when there's a borrow, and 1 when there isn't."
	  (let ((diff (- VX VY)))
	    (setf VX (mod (+ VY VX) *max-val*)
		  VF (if (< diff 0) 0 1))))
	 ("8XY6" 	"Shifts VX right by one. VF is set to the value of the least significant bit of VX before the shift.[2]"
	  (multiple-value-bind (div rem) (truncate VX 2)
	    (setf VX div VF rem)))
	 ("8XY7" 	"Sets VX to VY minus VX. VF is set to 0 when there's a borrow, and 1 when there isn't."
	  (let ((diff (- VY VX)))
	    (setf VX (mod (+ VY VX) *max-val*)
		  VF (if (< diff 0) 0 1))))
	 ("8XYE" 	"Shifts VX left by one. VF is set to the value of the most significant bit of VX before the shift.[2]"
	  (setf VF (ash VX -7)
	   VX (ash VX 1)))
	 ("9XY0" 	"Skips the next instruction if VX doesn't equal VY."
	  (if (/= VX VY) (next)))
	 ("ANNN" 	"Sets I to the address NNN."
	  (setf *index* N))
	 ("BNNN" 	"Jumps to the address NNN plus V0."
	  holdpc
	  (setf *pc* (+ N V0)))
	 ("CXNN" 	"Sets VX to a random number and NN."
	  (logand (random #xFF) N))
	 ("DXYN" 	"Draws a sprite at coordinate (VX, VY) that has a width of 8 pixels and a height of N pixels. Each row of 8 pixels is read as bit-coded (with the most significant bit of each byte displayed on the left) starting from memory location I; I value doesn't change after the execution of this instruction. As described above, VF is set to 1 if any screen pixels are flipped from set to unset when the sprite is drawn, and to 0 if that doesn't happen."
	  (setf VF 0)
	  (loop for left from 0 below 8 
	     with xdest = (+ left VX) do
	       (loop for down from 0 below N
		  with ydest = (+ down VY) 
		  with pixel = (logand (ash (aref *memory* (+ *index* down)) (- xdest)) 1)
		  do (symbol-macrolet ((it (aref *gfx* xdest ydest)))
		       (setf it (logxor it pixel))
		       (if (/= (logand it pixel) 0)
			   (setf VF 1))))))
	 ("EX9E" 	"Skips the next instruction if the key stored in VX is pressed."
	  (if (pressedp (aref *key* VX)) (next)))
	 ("EXA1" 	"Skips the next instruction if the key stored in VX isn't pressed."
	  (if (not (pressedp (aref *key* VX))) (next)))
	 ("FX07" 	"Sets VX to the value of the delay timer."
	  (setf VX *delay-timer*))
	 ("FX0A" 	"A key press is awaited, and then stored in VX.")
	 ("FX15" 	"Sets the delay timer to VX."
	  (setf *delay-timer* VX))
	 ("FX18" 	"Sets the sound timer to VX."
	  (setf *sound-timer* VX))
	 ("FX1E" 	"Adds VX to I.[3]"
	  (incf *index* VX)) ;what is the correct behavior if there's overflow?
	 ("FX29" 	"Sets I to the location of the sprite for the character in VX. Characters 0-F (in hexadecimal) are represented by a 4x5 font.")
	 ("FX33" 	"Stores the Binary-coded decimal representation of VX, with the most significant of three digits at the address in I, the middle digit at I plus 1, and the least significant digit at I plus 2. (In other words, take the decimal representation of VX, place the hundreds digit in memory at location in I, the tens digit at location I+1, and the ones digit at location I+2.)"
	  (setf (aref *memory* *index*) (floor X 100)
	   (aref *memory* (1+ *index*)) (mod (floor X 10) 10)
	   (aref *memory* (+ *index* 2)) (mod (mod X 100) 10)))
	 ("FX55" 	"Stores V0 to VX in memory starting at address I.[4]"
	  (loop for ctr from 0 to X
	     with dest = (+ *index* ctr)
	     do (setf (aref *memory* dest) (aref *registers* ctr))))
	 ("FX65" 	"Fills V0 to VX with values from memory starting at address I.[4]"
	  (loop for ctr from 0 to X
	     with dest = (+ *index* ctr)
	     do (setf (aref *registers* ctr) (aref *memory* dest)))))
     collect (destructuring-bind (match xmask ymask nmask)
		 (mapcar
		  (lambda (x) (read-from-string (concatenate 'string "#x" x)))
		  `(,(substitute-if #\F (lambda (x) (or (char= x #\X) 
						   (char= x #\Y)
						   (char= x #\N)))
				    opcode)
		     ,(map 'string (lambda (x) (if (char= x #\X) #\F #\0)) opcode)
		     ,(map 'string (lambda (x) (if (char= x #\Y) #\F #\0)) opcode)
		     ,(map 'string (lambda (x) (if (char= x #\N) #\F #\0)) opcode)))
	       `(lambda (opcode)
		  (and (= ,match (logior opcode ,(logior ymask (logior nmask xmask))))
		       (or (let ((X (ash (logand ,xmask opcode) -8))
			      (Y (ash (logand ,ymask opcode) -4))
			      (N (logand ,nmask opcode)))
			     (declare (ignorable X Y N))
			     ,@(if (eq (car body) 'holdpc)
				   (cdr body)
				   (append body
					   (list '(next)))))
			   t))))))

