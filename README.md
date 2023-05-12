# A Formally Verified Library of Double-Word Arithmetic
Copyright (c) 2023 Ariel Kellison

This library is open-source licensed according to the LGPL (Gnu Lesser General
Public License) version 3 or any later version.

## Repository map

- **dd_lib**: a C library for double-double arithmetic. 
- **accuracy_proofs**: a directory containing verified roundoff error analyses for double-word operations.
- **verif_proofs**: a directory containing VST proofs of correctness of the C functions from **dd_lib**. 
- **common**: a directory with of Coq files with common lemmas and tactics.

## How to build the proofs
In a Coq Platform that already has CompCert and VST installed, you must also install VSTlib and VCFloat.

Clone the repo https://github.com/VeriNum/vcfloat. In the directory **vcfloat/vcfloat/**
- `make -j`
- `make install` to move VCFloat to your Coq install (i.e., your-coq-installation/coq/user-contrib/VSTlib)

Clone the repo https://github.com/PrincetonUniversity/VST. In the directory **VST/lib/**
- `make -j`
- `make install` 

Now, in the main directory **double_double**:
- `make run-clightgen` to populate **verif_proofs/verif_objs/** with **.v** files containing the Clight ASTs from the C functions in **dd_lib** used in the VST proofs. 
- `make` to build the VST proofs in **verif_proofs/** and the accuracy proofs in **accuracy_proofs/**.

# On Building A Verified Library for Double-Word Arithmetic
## Introduction 

The IEEE 754-2008 standard[^c1] for floating-point arithmetic defines three binary formats, with word lengths of 32, 64, and 128 bits. Each binary format can represent a unique set of floating-point data, and is characterized by its precision ${(p \ge 2)}$ and exponent range ${(e_{min} < 0  < e_{max})}$.

| format |   p | emin | emax|
|---------|-----|-------|-----|
| binary32 | 24 | -126 | 127 | 
| binary64 | 53 | -1022 | 1023 |
| binary128| 113 | -16382 | 16383 |

The exact semantics for the basic arithmetic operations on these formats is defined by the standard, as is the notion of *correct rounding*, which specifies how the result of an operation on floating-point data should be modified to fit in the format: 

> *Except where stated otherwise, every operation shall be performed as if it first produced an intermediate result correct to infinite precision and with unbounded range, and then rounded to that result according to one of the [rounding] attributes in this clause.*

In principle, the standard enables proving *rounding error bounds* for numerical algorithms in a portable way:  any algorithm using the formats and basic operations defined in the standard should exhibit the exact same error due to rounding on any system that fully complies with the standard. 

In practice, full compliance with the standard can hinder performance. The binary format with the largest precision available on all commercially significant platforms is double-precision (binary64) but many calculations across disciplines require a significantly higher precision. While IEEE 754 compliant *quadruple*-precision (binary128) can be simulated in software, the slowdown can be significant in comparison to implementations of *double-word arithmetic* [^c2]. 

## Double-word arithmetic

Double-word arithmetic represents extra precise floating-point numbers using a pair of IEEE 754 compliant precision $p$ numbers. In all existing implementations, the underlying floating-point format is binary64. For this reason, double-word arithmetic is commonly referred to as *double-double*. Formally, a double-word number $x$ is the unevaluated sum $x_h + x_l$ of two floating-point numbers $x_h$ and $x_l$ such that $x_h = rnd(x)$, where $rnd$ denotes the application of an IEEE 754 compliant rounding operation. At first glance, this definition might appear a bit odd, but suppose we had an algorithm `2Sum` that computed both the result of adding two floating-point numbers $a$ and $b$ and the rounding error $s$ resulting from the addition. In this case, $a + b + s$ is a double-word: $a + b = rnd(a + b + s)$.   
## Double-Double Trouble

The trouble with double-double is that there is no well defined notion of *correct rounding*, which “breaks the logic and validity of error analyses”[^c2]. Consider the following example. 

If the result of a floating-point arithmetic operation is rounded using IEEE 754 `roundTiesToEven`, then the operation returns the floating-point number nearest to the infinitely precise result (ties breaking even), which is at a distance of at most a *unit roundoff* $u$; for binary formats with precision $p$, $u = 2^{-p}$. 

Unfortunately, double-word numbers composed of a pair of precision $p$ floating-point numbers are not equivalent to floating-point numbers with precision $2p$. For example, the floating-point number with precision 106 closest to $1.0$ is at a distance of at most $2^{-106}$ while the double-word closest to $1.0$ is $1.0 + 2^{-1022}$. The natural question we are left with is, which of these two numbers would constitute a correctly rounded result? Because we don’t have a clearly defined answer to this question, rounding error analyses for double-word arithmetic have historically been somewhat fraught; M. Joldes and co-authors [^c3] note that 

> *Many algorithms [for double-word arithmetic] have been published without a proof, or with error bounds that are sometimes loose, sometimes fuzzy, and sometimes unsure.*

##  A Verified Library for Double-Word Arithmetic

Building on recent work by Rideau and co-authors[^c4] that verified tight rounding error bounds for double-word arithmetic operations in [the Coq proof assistant](https://coq.inria.fr/), we are developing a verified C library for double-word arithmetic where every function in the library is directly connected to Coq proofs of its accuracy and correctness. We use the Flocq[^c5] library to prove the correctness and accuracy of algorithms (implemented in Coq) for double-word arithmetic and the Verified Software Toolchain[^c6] (VST) to prove that our C library correctly implements these algorithms. 

A library for double-word arithmetic supports (at a minimum) the following operations: the addition of a double-word number and a floating-point number, the addition of two double-word numbers, the multiplication of a double-word number by a floating-point number, the multiplication of two double-word numbers, the division of a double-word number by a floating-point number, and the division of two double-word numbers. These operations rely on three additional algorithms: `2Sum` (described above), `Fast2Sum` (a variation of `2Sum` that uses a fused multiply-add), and `Fast2Mult`. 

### Example: Addition of a double-word number and a floating-point number

We give an example of connecting C implementations of double-word operations to Coq proofs of their accuracy and correctness using the addition of a double-word number and a floating-point number. We implement this operation in Coq as  `DWPlusFP`, which is a function over three floating-point variables of type `ftype t`  where `t` is any floating-point precision:

``` Coq
(** Coq function for addition of a double-word number and a floating-point number *)
Definition DWPlusFP (xh xl y : ftype t ) := 
let (sh, sl) := 2Sum xh y in
let v:= BPLUS xl sl in
let (zh, zl) := Fast2Sum sh v in (zh, zl).
```
The `BPLUS` operation in the above definition of `DWPlusFP` denotes the addition of IEEE 754 binary  floating-point numbers as defined by Flocq.

#### Proving accuracy & correctness 

Proving that the `DWPlusFP` algorithm is *correct* entails showing that it returns a double-word number according to our Coq definition of a double-word:

``` Coq
(** Coq definition of a double-word *) 
Definition double_word : ftype t -> ftype t -> Type :=
  fun xh xl => FT2R xh = rounded t (FT2R xh + FT2R xl).
```
The function `FT2R` in the above definition of `double_word` is an injection from floating-point numbers to real numbers. 

Proving the  *accuracy* of the `DWPlusFP` algorithm follows by connecting our Coq implementation of `DWPlusFP` to previous work[^c4]. There is a complication to this: previous work does not use the IEEE 754 binary format defined in Flocq, it instead uses a Flocq format with no minimum exponent (see [Flocq formats](https://flocq.gitlabpages.inria.fr/theos.html#formats
) for more details). We therefore have to explicitly handle the treatment of underflow and overflow; if we assume some conditions on underflow, then we are able to prove the theorem `relative_error_DWPlusFP` using the previous formalization, which bounds the rounding error of the operation by twice the unit roundoff squared. 

``` Coq
Variables (xh xl y : ftype t).

Notation zh := (FT2R (fst (DWPlusFP xh xl y))).
Notation zl := (FT2R (snd (DWPlusFP xh xl y))).
Let xr  := (FT2R xh + FT2R xl).
Let yr  := (FT2R y).

Definition relative_error_DWPlusFP := Rabs (((zh + zl) - (xr  + yr)) / (xr  + yr)).
Notation u   := (bpow 2 (- precision t)).

Theorem relative_error_DWPlusFP : relative_error_DWPlusFP <= 2 * u ^ 2. Proof. … Qed.
```

#### Verifying the C function

Finally, we prove that the following C function correctly implements the Coq function  `DWPlusFP` using VST.
``` C
void dw_plus_dw(struct dword *st, struct dword *x, struct dword *y) {
   double v; double w; struct dword sh;
   two_sum(&sh,x->s,y->s);
   v      = x->t + y->t;
   w      = sh.t + v;
   fast_2sum(st,sh.s,w);
}
```
We do this by specifying and proving a Hoare triple ${Pre}$ `dw_plus_dw` ${Post}$, where the precondition $Pre$ and postcondition $Post$ are assertions of the form $PROP(P)$  $LOCAL(Q)$  $SEP(R)$ where $P$ is a Coq term of type $Prop$, $Q$ characterizes the values of local and global variables, and $R$ is a spatial assertion describing the contents of the heap. The specification for `dw_plus_dw` is given below as `dw_plus_fp_spec`. The meaning of this specification is, suppose the function is called with three parameters whose C-language types are pointer-to-struct, pointer-to-struct, and pointer-to-double. Suppose also that the data at the addresses associated with these types is properly initialized: the data at address $s$ is uninitialized and the data at address $x$ contains a double-word $xhl$. Then, after executing the function, the result stored at address $s$ is equivalent to the result of evaluating the Coq function `DWPlusFP` on the double-word $xhl$ and double precision float $y$, and the double-word stored at address $x$ remains unchanged. 
``` Coq
(** VST specification of dw_plus_dw *)
Definition f2val (pq: ftype Tdouble * ftype Tdouble) : val*val :=
 (Vfloat (fst pq), Vfloat (snd pq)).

Definition dw_plus_fp_spec := 
  DECLARE _dw_plus_fp
  WITH s: val, x : val, 
      xhl : ftype Tdouble * ftype Tdouble, y : ftype Tdouble
  PRE [tptr dword, tptr dword, tdouble ] 
    PROP()
    PARAMS (s; x; Vfloat y)
    SEP(data_at_ Tsh dword s; 
          data_at Tsh dword (f2val xhl) x) 
  POST [ tvoid ]
    PROP()
    RETURN()
    SEP(data_at Tsh dword 
          (f2val (DWPlusFP (fst xhl) (snd xhl) y)) s; 
        data_at Tsh dword (f2val xhl) x). 
```
The proof that `dw_plus_dw` satisfies this specification is very straightforward as there aren’t any loops or tricky data structures in the C function. You can read more about using VST in [Software Foundations Volume 5](https://softwarefoundations.cis.upenn.edu/vc-current/index.html).

## Conclusion 
It has been said that the speed advantage of double-word arithmetic makes it “‘an attractive nuisance,' like an unfenced backyard swimming pool”[^c2]. We note that a *verified* library for double-word arithmetic provides a *portable proof interface* for client programs, which we hope will make computing with double-words more attractive and less of a nuisance. 

Finally, we conclude by sharing a quote of Knuth’s[^c7], which we believe conveys a sentiment that applies well here, if one replaces “system programmers” with “logicians.”

> *Some people working in “higher levels” of numerical analysis will regard the topic treated here as the domain of system programmers. Other people working in “higher levels” of systems programming will regard the topic treated here as the domain of numerical analysts. But I hope that there are a few people left who will want to look carefully at these basics. Although the methods reside perhaps on a low level, they underlie all of the more grandiose applications of computers to numerical problems, so it is important to know them well.* 

[^c1]: "IEEE Standard for Floating-Point Arithmetic," in IEEE Std 754-2019 (Revision of IEEE 754-2008), 22 July 2019, doi: 10.1109/IEEESTD.2019.8766229.
[^c2]: “Design, implementation and testing of extended and mixed precision BLAS”, in ACM Transactions on Mathematical Software, 28(2), pp. 152–205, 01 June 2001, doi: 10.1145/567806.567808. 
[^c3]: “Tight and Rigorous Error Bounds for Basic Building Blocks of Double-Word Arithmetic,” in ACM Transactions on Mathematical Software, 44(2), pp. 1-27, 18 October 2017, doi: 10.1145/3121432.
[^c4]: “Formalization of Double-Word Arithmetic, and Comments on ‘Tight and Rigorous Error Bounds for Basic Building Blocks of Double-Word Arithmetic’,” in ACM Transactions on Mathematical Software, 48(1), pp. 1-24, 16 February, 2022, doi: 10.1145/3484514.
[^c5]: “Flocq: A Unified Library for Proving Floating-Point Algorithms in Coq,” in 2011 IEEE 20th Symposium on Computer Arithmetic, Tuebingen, Germany, 2011, pp. 243-252, doi: 10.1109/ARITH.2011.40.
[^c6]: “Program Logics for Certified Compilers,” Cambridge University Press,
USA (2014).
[^c7]: “The art of computer programming, volume 2 (3rd ed.): seminumerical algorithms,” Addison-Wesley Longman Publishing Co., Inc., USA (1997). 






















