(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** [Big] : a wrapper around ocaml [ZArith] with nicer names,
    and a few extraction-specific constructions *)

(** To be linked with [zarith] *)

type big_int = Z.t
    (** The type of big integers. *)

let zero = Z.zero
        (** The big integer [0]. *)

let one = Z.one
        (** The big integer [1]. *)

let two = Z.of_int 2
        (** The big integer [2]. *)

(** {6 Arithmetic operations} *)

let opp = Z.neg
        (** Unary negation. *)

let abs = Z.abs
        (** Absolute value. *)

let add = Z.add
        (** Addition. *)

let succ = Z.succ
(** Successor (add 1). *)

let add_int = Z.add
        (** Addition of a small integer to a big integer. *)

let sub = Z.sub
        (** Subtraction. *)

let pred = Z.pred
        (** Predecessor (subtract 1). *)

let mult = Z.mul
        (** Multiplication of two big integers. *)

let mult_int x y = Z.mul (Z.of_int x) y
        (** Multiplication of a big integer by a small integer *)

let square x = Z.mul x x
        (** Return the square of the given big integer *)

let sqrt = Z.sqrt
        (** [sqrt_big_int a] returns the integer square root of [a],
           that is, the largest big integer [r] such that [r * r <= a].
           Raise [Invalid_argument] if [a] is negative. *)

let quomod = Z.div_rem
        (** Euclidean division of two big integers.
           The first part of the result is the quotient,
           the second part is the remainder.
           Writing [(q,r) = quomod_big_int a b], we have
           [a = q * b + r] and [0 <= r < |b|].
           Raise [Division_by_zero] if the divisor is zero. *)

let div = Z.div
        (** Euclidean quotient of two big integers.
           This is the first result [q] of [quomod_big_int] (see above). *)

let modulo = Z.(mod)
        (** Euclidean modulus of two big integers.
           This is the second result [r] of [quomod_big_int] (see above). *)

let gcd = Z.gcd
        (** Greatest common divisor of two big integers. *)

let power = Z.pow
        (** Exponentiation functions.  Return the big integer
           representing the first argument [a] raised to the power [b]
           (the second argument).  Depending
           on the function, [a] and [b] can be either small integers
           or big integers.  Raise [Invalid_argument] if [b] is negative. *)

(** {6 Comparisons and tests} *)

let sign = Z.sign
        (** Return [0] if the given big integer is zero,
           [1] if it is positive, and [-1] if it is negative. *)

let compare = Z.compare
        (** [compare_big_int a b] returns [0] if [a] and [b] are equal,
           [1] if [a] is greater than [b], and [-1] if [a] is smaller
           than [b]. *)

let eq = Z.equal
let le = Z.leq
let ge = Z.geq
let lt = Z.lt
let gt = Z.gt
        (** Usual boolean comparisons between two big integers. *)

let max = Z.max
        (** Return the greater of its two arguments. *)

let min = Z.min
        (** Return the smaller of its two arguments. *)

(** {6 Conversions to and from strings} *)

let to_string = Z.to_string
        (** Return the string representation of the given big integer,
           in decimal (base 10). *)

let of_string = Z.of_string
        (** Convert a string to a big integer, in decimal.
           The string consists of an optional [-] or [+] sign,
           followed by one or several decimal digits. *)

(** {6 Conversions to and from other numerical types} *)

let of_int = Z.of_int
        (** Convert a small integer to a big integer. *)

let is_int = Z.fits_int
        (** Test whether the given big integer is small enough to
           be representable as a small integer (type [int])
           without loss of precision.  On a 32-bit platform,
           [is_int_big_int a] returns [true] if and only if
           [a] is between 2{^30} and 2{^30}-1.  On a 64-bit platform,
           [is_int_big_int a] returns [true] if and only if
           [a] is between -2{^62} and 2{^62}-1. *)

let to_int = Z.to_int
        (** Convert a big integer to a small integer (type [int]).
           Raises [Failure "int_of_big_int"] if the big integer
           is not representable as a small integer. *)

(** Functions used by extraction *)

let double x = mult_int 2 x
let doubleplusone x = succ (double x)

let nat_case fO fS n = if sign n <= 0 then fO () else fS (pred n)

let positive_case f2p1 f2p f1 p =
 if le p one then f1 () else
   let (q,r) = quomod p two in if eq r zero then f2p q else f2p1 q

let n_case fO fp n = if sign n <= 0 then fO () else fp n

let z_case fO fp fn z =
  let s = sign z in
  if s = 0 then fO () else if s > 0 then fp z else fn (opp z)

let compare_case e l g x y =
  let s = compare x y in if s = 0 then e else if s<0 then l else g

let nat_rec fO fS =
  let rec loop acc n =
    if sign n <= 0 then acc else loop (fS acc) (pred n)
  in loop fO

let positive_rec f2p1 f2p f1 =
  let rec loop n =
    if le n one then f1
    else
      let (q,r) = quomod n two in
      if eq r zero then f2p (loop q) else f2p1 (loop q)
  in loop

let z_rec fO fp fn = z_case (fun _ -> fO) fp fn
