Require Import Verse.
Require Vector.
Import VectorNotations.
Require Verse.Arch.C.

(** printing Xt %X^t%  #X<sup>t</sup>#            *)
(** printing Xti %X^{t-i+1}%  #X<sup>t-i+1</sup># *)
(** printing GF %\ensuremath{\mathbb{F}}%  #𝔽#                 *)

(** printing Two32  %2^{32}%  #2<sup>32</sup>#  *)
(** printing Two64  %2^{64}%  #2<sup>64</sup>#  *)
(** printing Two96  %2^{96}%  #2<sup>96</sup>#  *)
(** printing Two128 %2^{128}% #2<sup>128</sup># *)
(** printing Two130 %2^{130}% #2<sup>130</sup># *)
(** printing Two32ij %2^{32 (i + j)}% #2<sup>32(i+j)</sup># *)
(** printing Two32ij4 %2^{32 (i + j - 4)}% #2<sup>32(i+j - 4)</sup># *)
(** printing Two2 %2^{2}% #2<sup>2</sup># *)

(** printing C0 %C_0% #C<sub>0</sub>#   *)
(** printing C1 %C_1% #C<sub>1</sub># *)
(** printing C2 %C_2% #C<sub>2</sub># *)
(** printing Ct %C_t% #C<sub>t</sub># *)
(** printing Ci %C_i% #C<sub>i</sub># *)

(** printing Mt %M_t% #M<sub>t</sub># *)
(** printing Mi %M_i% #M<sub>i</sub># *)

(** printing a0 %a_0% #a<sub>0</sub># *)
(** printing a1 %a_1% #a<sub>1</sub># *)
(** printing a2 %a_2% #a<sub>2</sub># *)
(** printing a3 %a_3% #a<sub>3</sub># *)
(** printing a4 %a_4% #a<sub>4</sub># *)
(** printing ai %a_t% #a<sub>i</sub># *)

(** printing r0 %r_0% #r<sub>0</sub># *)
(** printing r1 %r_1% #r<sub>1</sub># *)
(** printing r2 %r_2% #r<sub>2</sub># *)
(** printing r3 %r_3% #r<sub>3</sub># *)
(** printing r4 %r_4% #r<sub>4</sub># *)
(** printing rp0 %r'_0% #r′<sub>0</sub># *)
(** printing rp1 %r'_1% #r′<sub>1</sub># *)
(** printing rp2 %r'_2% #r′<sub>2</sub># *)
(** printing rp3 %r'_3% #r′<sub>3</sub># *)
(** printing rpi %r'_i% #r′<sub>i</sub># *)
(** printing r4 %r_4% #r<sub>4</sub># *)

(** printing ri %r_i% #r<sub>i</sub># *)
(** printing rj %r_j% #r<sub>j</sub># *)
(** printing rjprim %r_j^'% #r′<sub>j</sub># *)

(** printing p0 %p_0% #p<sub>0</sub># *)
(** printing p1 %p_1% #p<sub>1</sub># *)
(** printing p2 %p_2% #p<sub>2</sub># *)
(** printing p3 %p_3% #p<sub>3</sub># *)
(** printing p4 %p_4% #p<sub>4</sub># *)
(** printing pi %p_i% #p<sub>i</sub># *)
(** printing pi1 %p_{i+1}% #p<sub>i+1</sub># *)

(** * The poly1305 message hash.

Let [GF] denote the finite field GF(2¹³⁰ - 5). The poly1305 MAC in
essence is just the evaluation of the message thought of as a
polynomial over the finite field [GF]. Elements of this field can be
represented using 130 bit word. To get the polynomial corresponding to
the message [M], we divide it into blocks [Mi] of 16 byte (128-bits)
with the possibility of the last block [Mt] to be of less than 16
bytes. The message [M] is then considered as the polynomial

[ M(X) = C1 Xt + ... + Ci Xti + ... + Ct X].

where the coefficient [Ci] is the element in [GF] whose least
significant bits are that of [Mi] with an additional 1-bit appended to
it. Thus the length of Ci in bits is one more than that of [Mi].

The poly1305 MAC for secrets [R] and [K] consists of computing [M(R) +
K] rounded to 128 bits. At the heart of any fast implementations is
therefore the Horner's method of evaluation of a polynomial: keep an
accumulator [A] which starts with 0 and is updated using the step [A
:= (A + Ci) * R]

 *)

Definition Word       := Word64.
Definition BLOCK_SIZE := 2.
Definition Block      := Array BLOCK_SIZE littleE Word.


(** ** Arithmetic over [GF].

In C the biggest supported word type is the type of 64-bit word. This
means that we would need multiple 64-bit "Limbs" to represent a single
element of [GF]. Also we need to have enough left over bits so as to
ensure that bits do not overflow during arithmetic and that we
propagate carries correctly. We need enough additional vacant bits in
the 64-bit limbs so that the update [A = (A + Ci) * R] can be done
without overflows.

 *)

Definition Limb    := Word64.

(**

The poly1305 standard enforces that the parameter [R] in [GF] is of
128-bit. To facilitate the use of 64-bit limbs it is additionally
enforced that certain bits of [R] are zeros. If [R] in base 2³² is
expressed as

[R = r0 + r1 * Two32 + r2 * Two64 + r3 * Two96.]

Then the restrictions on [ri] are

- The most significant 4-bits of [ri] are all zero.

- All except r₀ have their bottom 2-bits as zero.


With these restrictions in place we can perform the Horner's step by
representing elements of [GF] as 5x64-bit limbs where the first 4
limbs contain 32-bits each and the last one contains the two remaining
bits making a total of 130 bits.


We define the Verse type that can capture such an element.

*)

Definition ElemArray := Array 5 hostE Limb.
Definition RArray    := Array 4 hostE Limb.


(*

Require Import Semantics.NSemantics.
Import NSemanticsTactics.
Import NArith.
Module Internal.

*)

Module Internal.
  Section Poly1305.
    (** Let us start by parameterising over the program variables. *)
    Variable progvar : VariableT.
    Definition ElemIndex := VarIndex progvar 5 Limb.
    Arguments progvar [k] _.


    Variable Accum : progvar ElemArray.

    Definition params : Declaration := [Var Accum].

    (** Variables that keep track of the accumulator *)
    Variables a0 a1 a2 a3 a4 : progvar Limb.

    (** Variables that keep track of the R values *)
    Variables r0 r1 r2 r3    : progvar Limb.

    (** The limbs that capture the result of product *)
    Variable p0 p1 p2 p3 p4 : progvar Limb.

    (** Variables to read the coefficient of the polynomial *)
    Variable C0 C1 : progvar Limb.

    Definition Select32 : constant Limb := Ox "00:00:00:00 FF:FF:FF:FF".


    (** *** Computing [A := A * R]

        We need to multiply the quantities

        [A = a0 + a1 * Two32 + a2 * Two64 + a3 * Two96 + a4 Two128]
        with

        [R = r0 + r1 * Two32 + r2 * Two64 + r3 * Two96 ]

        There is a total of 20-terms of the form [ai * rj * Two32ij
        ]. When (i + j >= 4), [Two32ij = Two128 * Twoij4] together
        with an additional [Two2] from [rj = rj/4 * 4] gives a term of
        the kind [Two130]. However in the field [GF], [Two130 = 5] and
        hence the ij-th term in the product gives [5 * ai * (rj/4)]
        Twoij4]. Since the two lower order bits of [rj] are zeros
        (except when j = 0), we can shift them without really worrying
        about loosing bits. The product is given by

        [p = p0 + p1 Two32 + p2 Two64 + p3 Two96 + p4 * Two128]

        where

        [p4 = a4 * r0 & 3]

        [p0 = a0 * r0 + a1 * rp3 + a2 * rp2 + a3 * rp1 + a4 * rp0 ]

        [p1 = a0 * r1 + a1 * r0 + a2 * rp3 + a3 * rp2 + a4 * rp1 ]

        [p2 = a0 * r2 + a1 * r1 + a2 * r0 + a3 * rp3 + a4 * rp2 ]

        [p3 = a0 * r3 + a1 * r2 + a2 * r1 + a3 * r0 + a4 * rp3 ]

        [rpi = ri >> 2 = ri/4]. Note that we do not loose any of the
        bits of [r1],[r2], and [r3]. The two bits lost from [r0] is
        accounted for in [p4].

        We require that each [a0..a3] should be at-most 33-bit (1
        additional bit that comes from adding the coefficient of the
        polynomial) and [a4] is at-most 4 bits.

     *)

    Definition Select2 : constant Limb := Ox "00:00:00:00 00:00:00:03".
    Definition five     : constant Limb := Ox "00:00:00:00 00:00:00:05".
    Definition MulR : code progvar
      :=
        [
          (** Summing up terms of the kind [ai * rj * Two32ij] for [i+j < 4] *)
          p0 ::= a0 * r0;

          p1 ::= a0 * r1;
          C0 ::= a1 * r0; p1 ::=+ C0;

          p2 ::= a0 * r2;
          C0 ::= a1 * r1; p2 ::=+ C0;
          C0 ::= a2 * r0; p2 ::=+ C0;

          p3 ::= a0 * r3;
          C0 ::= a1 * r2; p2 ::=+ C0;
          C0 ::= a2 * r1; p2 ::=+ C0;
          C0 ::= a3 * r0; p2 ::=+ C0;

          (** Summing up terms of the kind [ai * rj * Two32ij] for
              [i+j >= 4]. So we divide them by 4 (i.e. right shift by 2)
              and multiply by [Two130 = 5]. Shifting by 2 does not
              lead to any loss of bits except for [r0] which we handle
              first.
           *)

          p4 ::= r0 & Select2; p4 ::=* a4;

          C0 ::= r0 >> 2; C0 ::=* five;
          C1 ::= a4 * C0; p0 ::=+ C1;

          C0 ::= r1 >> 2; C0 ::=+ r1; (* C0 = (r1 >> 2) * 5 *)
          C1 ::= a3 * C0; p0 ::=+ C1;
          C1 ::= a4 * C0; p1 ::=+ C1;

          C0 ::= r2 >> 2; C0 ::=+ r2 ; (* C0 = (r2 >> 2) * 5 *)
          C1 ::= a2 * C0; p0 ::=+ C1;
          C1 ::= a3 * C0; p1 ::=+ C1;
          C1 ::= a4 * C0; p2 ::=+ C1;

          C0 ::= r3 >> 2; C0 ::=+ r3;  (* C0 = (r3 >> 2) * 5 *)
          C1 ::= a1 * C0; p0 ::=+ C1;
          C1 ::= a2 * C0; p1 ::=+ C1;
          C1 ::= a3 * C0; p2 ::=+ C1;
          C1 ::= a4 * C0; p3 ::=+ C1
        ]%list.


    (** *** Carry propagation and reduction modulo [Two130 - 5].

        Recall that an element of [GF] can be stored with 32-bits each
        in registers [a0..a3] and the remaining 2 bits in [a4]. After
        computation of the product the registers [p0..p3] have about
        62-bits and [p4] has about 5-bits. We cannot use this directly
        for the next Horner's step as there would be overflows. We
        adjust them by

        1. Propagating the carries from [pi] to [pi1]

        2. Reduce modulo [Two130 - 5].

        The reduction modulo [Two130 - 5] is essentially like a
        "carry" from [p4] to [p0]. We need to propagate the bits of
        [p4] other than the 2 least significant bits with a
        multiplicative factor of [5] as the element can be seen as
        [Two130 * (p4 >> 2)].

        The goal is to perform enough carry propagation and reduction
        so as to ensure that that the bits in [a0,...,a3] continue to
        be 32-bits and [a4] has at-most 3-bits. This is sufficient to
        make sure that there is no overflow during the product
        calculation in the next step.

        It is crucial to decide where to start and end the carry
        propagation.  Where ever we end, it can potentially have 1-bit
        more than the desired limit.  We therefore start the carry
        propagation from [p3] so that when we terminate, all the
        [a0..a3] will have 32-bits each and [a4] 3-bits (one more than
        the ideal 2-bits).

     *)
    Definition CarryPropogate : code progvar
      := [ C0 ::= p3 >> 32; p3 ::=& Select32; p4 ::=+ C0;
           C0 ::= p4 >> 2;  p4 ::=& Select2 ; C0 ::=* 5; p0 ::=+ C0;
           C0 ::= p0 >> 32; a0 ::= p0 & Select32; p1 ::=+ C0;
           C0 ::= p1 >> 32; a1 ::= p1 & Select32; p2 ::=+ C0;
           C0 ::= p2 >> 32; a2 ::= p2 & Select32; p3 ::=+ C0;
           C0 ::= p3 >> 32; a3 ::= p3 & Select32;
           a4 ::= p4 + C0
         ]%list.

  (** *** Handling input.

      When computing the poly1305 MAC, we need to take each
      successive block of data, convert into the appropriate
      coefficient of [GF] and add it to the accumulator for the
      Horner's method. We have two variants of the code where the
      first just adds the 128 bits directly. The other also increments
      the 129th bit (remember it is set to 1 for a full block).  When
      handling the last block we should use [Add128] with the
      assumption that the padding is done properly. Otherwise, we should
      use the [AddFullblock]

  *)
    Definition Add128 (blk : progvar Block) : code progvar.
      verse [ (* The first two limbs *)

          C1 ::==  blk[- 0 -];
          C0 ::=   C1 & Select32;
          C1 ::=>> 32;
          a0 ::=+  C0;
          a1 ::=+  C1;

          (** The next two limbs *)

          C1 ::==  blk[- 1 -];
          C0 ::=   C1 & Select32;
          C1 ::=>> 32;
          a2 ::=+ C0;
          a3 ::=+ C1
        ]%list.
    Defined.
    Definition AddFullBlock (blk : progvar  Block) : code progvar
      := Add128 blk ++ [ ++ a4 ]%list.


    (** The parameter [r] used in Poly1305 has certain 22-bits set to
      zero. Converting an arbitrary 128-bit word to such a form is
      called clamping. The rules of clamping is the following.

     - Among the least 32-bits the top 4 bits is cleared.

     - Among the other 3 32-bits, the top 4 and the bottom 2-bits are
       cleared.

   *)


   Definition clamp (blk : progvar Block) : code progvar.
     verse [
         C0 ::== blk[- 0 -];
         C0 ::=& Ox "0f:ff:ff:fc 0f:ff:ff:ff";
         MOVE C0 TO blk[- 0 -];

         C0 ::== blk[- 1 -];
         C0 ::=& Ox "0f:ff:ff:fc 0f:ff:ff:fc";
         MOVE C0 TO blk[- 1 -]
       ]%list.
   Defined.
   Definition regClamp : Declaration := [Var C0]%vector.
   Definition clampIter : iterator Block progvar
     := {| setup    := []%list;
           process  := clamp;
           finalise := []%list
        |}.

  End Poly1305.


  Import Verse.Arch.C.
  Definition prototypeClamp (fname : string) : Prototype CType + {Compile.CompileError}.
    Compile.iteratorPrototype Block fname Empty.
  Defined.

  Definition cRegsClamp := (- cr uint64_t "temp" -).

  Definition implementationClamp (fname : string) : Doc + {Compile.CompileError}.
    Compile.iterator Block fname Empty Empty regClamp.
    assignRegisters cRegsClamp.
    statements clampIter.
  Defined.

Definition clampName (fname : string) := fname ++ "_clamp".
Definition implementation (fname : string) : Doc + {Compile.CompileError} :=
  implementationClamp (clampName fname).

Definition prototypes fname :=
    clampProto <- prototypeClamp (clampName fname);
      {- [ clampProto ]%list -}.

End Internal.

Require Import Verse.Extraction.Ocaml.
Require Import Verse.CryptoLib.Names.
Require Import Verse.CryptoLib.Names.

Definition implementation_name : Name := {| primitive := "poly1305";
                                            arch      := "c";
                                            features  := ["portable"]
                                         |}%string.

Definition cname     := cFunName implementation_name.
Definition cfilename := libVerseFilePath implementation_name.

Definition implementation : unit
  := writeProgram (C cfilename) (Internal.implementation cname).

Definition prototypes
  := recover (Internal.prototypes cname).

Require Import Verse.FFI.Raaz.

Definition raazFFI : unit :=
  let module := raazModule implementation_name in
  write_module module (List.map ccall prototypes).
