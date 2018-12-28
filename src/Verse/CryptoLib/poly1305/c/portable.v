
(** printing Xt %X^t%  #X<sup>t</sup>#            *)
(** printing Xti %X^{t-i+1}%  #X<sup>t-i+1</sup># *)
(** printing GF %\ensuremath{\mathbb{F}}%  #𝔽#                 *)

(** printing alpha %\alpha% #α#  *)
(** printing beta  %\beta%  #β#  *)
(** printing Two32  %2^{32}%  #2<sup>32</sup>#  *)
(** printing Two64  %2^{64}%  #2<sup>64</sup>#  *)
(** printing Two96  %2^{96}%  #2<sup>96</sup>#  *)
(** printing Two128 %2^{128}% #2<sup>128</sup># *)
(** printing Two130 %2^{130}% #2<sup>130</sup># *)
(** printing Two131 %2^{131}% #2<sup>131</sup># *)
(** printing Two32ij %2^{32 (i + j)}% #2<sup>32(i+j)</sup># *)
(** printing Two32ij4 %2^{32 (i + j - 4)}% #2<sup>32(i+j - 4)</sup># *)
(** printing Two2 %2^{2}% #2<sup>2</sup># *)
(** printing Twon %2^{n}% #2<sup>n</sup># *)

(** printing C0 %C_0% #C<sub>0</sub>#   *)
(** printing C1 %C_1% #C<sub>1</sub># *)
(** printing C2 %C_2% #C<sub>2</sub># *)
(** printing Ct %C_t% #C<sub>t</sub># *)
(** printing Ci %C_i% #C<sub>i</sub># *)

(** printing T0 %T_0% #T<sub>0</sub># *)
(** printing T1 %T_1% #T<sub>1</sub># *)

(** printing Mt %M_t% #M<sub>t</sub># *)
(** printing Mi %M_i% #M<sub>i</sub># *)

(** printing a0 %a_0% #a<sub>0</sub># *)
(** printing a1 %a_1% #a<sub>1</sub># *)
(** printing a2 %a_2% #a<sub>2</sub># *)
(** printing a3 %a_3% #a<sub>3</sub># *)
(** printing a4 %a_4% #a<sub>4</sub># *)
(** printing ai %a_t% #a<sub>i</sub># *)
(** printing ai1 %a_{i+1}% #a<sub>i+1</sub># *)

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


Require Import Verse.
Require Vector.
Import VectorNotations.
Require Verse.Arch.C.

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
it. Thus the length of [Ci] in bits is one more than that of [Mi].

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

The poly1305 standard enforces that the parameter [R] in [GF] is of
128-bit. To facilitate the use of 64-bit limbs it is additionally
enforced that certain bits of [R] are zeros. If [R] in base 2³² is
expressed as

[R = r0 + r1 * Two32 + r2 * Two64 + r3 * Two96.]

Then the restrictions on [ri] are

- The most significant 4-bits of [ri] are all zero.

- All except r₀ have their bottom 2-bits as zero.


We have the following representation of for the value R and the
accumulator A.

- The quantity [R] is represented as 4x64-bit registers [r0,..,r3]
  where each [ri] contains 32-bits each. Due to the restrictions on
  the allowed value of [R], each of the [ri]' have only the least 28
  bit significant.

- The accumulator [A] can hold arbitrary element of [GF] which
  requires 130-bits. We divide these 130 bits into registers [a0..a4]
  as follows.

  - Registers [a0..a3] contains 32-bits each thereby accounting for
    the least significant 128-bits.

  - The register [a4] contains the remaining 2-bits.

*)

Definition Limb      := Word64.

(** The masks that are required when selecting bits during. field
    arithmetic.
*)
Definition Select32 : constant Limb := Ox "00:00:00:00 FF:FF:FF:FF".
Definition Select2  : constant Limb := Ox "00:00:00:00 00:00:00:03".

(** *** Managing the accumulator during evaluation.

Although all elements in [GF] can be reduced to the standard form that
we described above, during the evaluation of the MAC, we maintain a
slightly looser bound on the number of significant bits in [a4]. At
the start of any of the update, we maintain the invariant that
[a0..a3] have 32-bits each as in the standard form but [a4] has at
most 3 significant bits (i.e one more than that in the standard
form). This will ensure that no overflows happen when performing the
update [A := (A + C) * R]. However, as a result of the update the
invariant on [a0..a4] will be violated. We restore this with a single
carry propagation and reduction.

As a final step, after all the coefficients of the message polynomial
has been processed, we perform a full modular reduction.

*)


Module Internal.

  Section Poly1305.

    (**  * Program variables.

    Let us start by parameterising over the program variables.

     *)

    Variable progvar : VariableT.
    Arguments progvar [k] _.

    (** We define type aliases for some of the types that are relevant
        for poly1305. See the arithmetic section on the rationale for
        these choices. The arrays are packed representations where as
        their indices are split up into 32-bit chunks.
     *)


    Definition ElemArray := Array 3 hostE Limb.
    Definition Array128  := Array 2 hostE Limb.

    Definition ElemIndex := VarIndex progvar 5 Limb.
    Definition RIndex    := VarIndex progvar 4 Limb.


    (** ** Parameters.

       We have three functions exposed from this module.

        1. A poly1305 iterator that incrementally process multiples of
           blocks. This iterator is used while incrementally
           processing blocks and the entire message is not yet seen.
           The only parameters for this iterator is the array holding
           the accumulator ([AArray]), the array holding the value [r]
           ([RArray]).

        2. A poly1305 iterator that in addition to processing of
           multiple of blocks also finalises the message hash. This is
           used where dealing with messages which are exact multiples
           of the block length. The parameters for this iterator is
           the array holding the accumulator ([AArray]), the array
           holding the value [r] ([RArray]), and the array holding
           value [s] ([SArray]).

        3. A poly1305 last block processing function. This function
           should be used only for processing messages that have an
           incomplete last block. This function however expects its
           input buffer to be the size of a single block which in
           addition is appropriately padded.  The parameters for this
           function is the message buffer [LastBlock] having size
           at-least 16-bytes holding the padded message, the array
           holding the accumulator ([AArray]), the array holding the
           value [r] ([RArray]), and the array holding value [s]
           ([SArray]).

        4. The clamping function for generating valid poly1305 keys
           [r].

        They have slightly different parameters and hence we have
        different names for the list.

     *)

    Variable LastBlock : progvar Block.
    Variable AArray    : progvar ElemArray.
    Variable RArray    : progvar Array128.
    Variable SArray    : progvar Array128.

    Definition paramsIncremental : Declaration
      := [Var AArray; Var RArray].
    Definition paramsBlockMac    : Declaration
      := [Var AArray; Var RArray; Var SArray].
    Definition paramsPartialMac   : Declaration
      := [Var LastBlock; Var AArray; Var RArray; Var SArray].
    Definition paramsClamp       : Declaration := Empty.

    (** ** Registers.

        Except for the clamping function all the other functions have
        similar register usage. We keep a working copy of the
        accumulator in the registers [a0,...,a4], the poly1305
        parameter [r] in the registers [r0,..,r3]. We also need
        registers [p1,..,p4] to help us compute the product
        [A*R]. Besides we need some temporary registers [T0] and [T1].
        We also define register caches [A] and [R] for ease of coding
        with these registers.

        The clamping function only needs the temporary variable [T0]
        as its register

     *)

    Variables a0 a1 a2 a3 a4 : progvar Limb.
    Variables r0 r1 r2 r3    : progvar Limb.
    (** The limbs that capture the result of product *)
    Variable p1 p2 p3 p4 : progvar Limb.

    (** Temporary variables that is used often *)
    Variable T0 T1 : progvar Limb.

    Definition register : Declaration
      := Vector.map Var [ a0; a1; a2; a3; a4;
                          r0; r1; r2; r3;
                          p1; p2; p3; p4;
                          T0; T1
                        ].


    Definition A : VarIndex progvar 5 Limb := varIndex [a0; a1; a2; a3; a4].
    Definition R : VarIndex progvar 4 Limb := varIndex [r0; r1; r2; r3].

    Definition LoadA : code progvar.
      verse [ a1 ::=  AArray [- 0 -];
              a0 ::=  a0 & Select32;
              a1 ::=>> 32;

              a3 ::= AArray[- 1 -];
              a2 ::= a3 & 32;
              a3 ::=>> 32;

              a4 ::= AArray[- 2 -]
            ]%list.
    Defined.

    Definition StoreA  : code progvar.
      verse [ T0 ::= a1 << 32;
              T0 ::=| a0;
              MOVE T0 TO AArray[- 0 -];
              T0 ::= a3 << 32;
              T0 ::=| a2;
              MOVE T0 TO AArray[- 1 -];
              MOVE a4 TO AArray[- 2 -]
            ]%list.
      Defined.
      Definition LoadR : code progvar.
        verse [ r0 ::=  RArray [- 0 -];
                r1 ::=  a0 >> 32;
                r0 ::=& Select32;
                r2 ::= RArray[- 1 -];
                r3 ::= a2 >> 32;
                r2 ::=& Select32
              ]%list.
      Defined.


    (** * The Horner's step as subroutines.

        The main step in the poly1305 computation is the update of the
        accumulator using the [A := (A + C) * R] step where [C] is the
        current block treated as a polynomial coefficient. We break up
        this step into three parts.

        - Adding the coefficient

        - Multiplying by R

        - Propagating carry and reduction mod [Two130 - 5].

     *)

    (** ** Adding 128-bit to accumulator.

       There are two variants of this function. The first variant just
       adds the block as 128-bit element of the field [GF]. The next
       also increments the 129th bit. The former can be used when
       handling the last partial block (padded appropriately) where as
       the latter is used for complete blocks. No carry propagation is
       done by these code.

     *)


    Definition Add128 {e : endian}(blk : progvar (Array 2 e Word64)) : code progvar.
      verse [ (* The first two limbs *)

          T1 ::=  blk[- 0 -];
          T0 ::=  T1 & Select32;
          T1 ::=>> 32;
          a0 ::=+  T0;
          a1 ::=+  T1;

          (** The next two limbs *)

          T1 ::=  blk[- 1 -];
          T0 ::=  T1 & Select32;
          T1 ::=>> 32;
          a2 ::=+ T0;
          a3 ::=+ T1
        ]%list.
    Defined.

    Definition AddFullBlock (blk : progvar Block) : code progvar
      := Add128 blk ++ [ ++ a4 ]%list.

    (** ** Computing [A := A * R]

        We need to multiply the quantities

        [A = a0 + a1 * Two32 + a2 * Two64 + a3 * Two96 + a4 Two128]
        with

        [R = r0 + r1 * Two32 + r2 * Two64 + r3 * Two96 ]

        There is a total of 20-terms of the form [ai * rj * Two32ij
        ]. When (i + j >= 4), [Two32ij = Two128 * Two32ij4] together
        with an additional [Two2] from [rj = rj/4 * 4] gives a term of
        the kind [Two130]. However in the field [GF], [Two130 = 5] and
        hence the ij-th term in the product gives [5 * ai * (rj/4)
        Two32ij4]. Since the two lower order bits of [rj] are zeros
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

        We now give the function for multiplying the accumulator with
        [R].  The expected input is such that each [a0..a3] should be
        at-most 33-bit (1 additional bit that comes from adding the
        coefficient of the polynomial) and [a4] is at-most 4 bits.

        A note on the variables

        We have variables for p1,p2,p3 and p4 only. The value of p0 is
        computed in a0 directly because we can arrange the operations
        such that a0 is no more used when we want to compute p0.

     *)
    Definition MulR : code progvar
      :=
        [
          (** Summing up terms of the kind [ai * rj * Two32ij] for [i+j < 4] *)


          (** *** [p3 = a0 r3 + a1 r2 + a2 r1 + a3 r0] *)

          p3 ::= a0 * r3;
          T0 ::= a1 * r2; p3 ::=+ T0;
          T0 ::= a2 * r1; p3 ::=+ T0;
          T0 ::= a3 * r0; p3 ::=+ T0;

          (** *** [p2 = a0 r2 + a1 r1 + a2 r0] *)
          p2 ::= a0 * r2;
          T0 ::= a1 * r1; p2 ::=+ T0;
          T0 ::= a2 * r0; p2 ::=+ T0;

          (** *** [p1 = a0 r1 + a1 r0] *)
          p1 ::= a0 * r1;
          T0 ::= a1 * r0; p1 ::=+ T0;

          (** *** [p0 = a0 * r0 ; a0 := p0] *)

          a0 ::=* r0;

          (** Summing up terms of the kind [ai * rj * Two32ij] for
              [i+j >= 4].
           *)

          (** *** Terms of the kind [ai * r3 * Two32ij].

              At this point the product component [p0] is already in
              [a0]. Also we do not need [a1] after the contribution of
              [r3] to [a0] has been computed. So we update [a1]
              directly and the product component [p1] is now in [a1].

           *)
          T0 ::= r3 >> 2; T0 ::=+ r3;
          T1 ::= a1 * T0; a0 ::=+ T1;
          T1 ::= a2 * T0; a1 ::= p1 + T1;
          T1 ::= a3 * T0; p2 ::=+ T1;
          T1 ::= a4 * T0; p3 ::=+ T1;

          (** *** Terms of the kind [ai * r2 * Two32ij]

              At this point the product components [p0] and [p1] are
              already in [a0] and [a1]. As before we will free up [a2]
              hence update [a2] directly.

           *)
          T0 ::= r2 >> 2; T0 ::=+ r2 ;
          T1 ::= a2 * T0; a0 ::=+ T1;
          T1 ::= a3 * T0; a1 ::=+ T1;
          T1 ::= a4 * T0; a2 ::= p2 + T1;

         (** *** Terms of the kind [ai * r1 * Two32ij].  *)
          T0 ::= r1 >> 2; T0 ::=+ r1;
          T1 ::= a3 * T0; a0 ::=+ T1;
          T1 ::= a4 * T0; a1 ::=+ T1;


          (** *** Terms of the kind [ai * r0 * Two32ij]  *)
          T0 ::= r0 >> 2; T0 ::=* 5;
          T1 ::= a4 * T0; a0 ::=+ T1;

          (** *** Setting [a3] and [a4].

              The two bits that we lost when shifting [r0] contributes
              to [a4] where as [a3] is just [p3] at this point.  *)

          a3 ::= p3;
          p4 ::= r0 & Select2; a4 ::=* p4
        ]%list.



    (** * Controlling overflows.

    The sizes of the registers and the constants have been so chosen
    that a single Horner step does not lead to any overflows. As
    described in above, we can successfully compute the next step if
    and only if maintain the invariant that the registers [a0..a3]
    have 32-bits each and [a4] has 3 bits. This we maintain by
    performing carry propagation and reduction modulo [Two130 - 5].

     *)


    (** ** Propagating carries and Reductions.

        An element of [GF] can be stored with 32-bits each in
        registers [a0..a3] and the remaining 2 bits in [a4]. After
        arithmetic, we often need to propagate carries. Also the bits
        beyond the least two bits in [a4] contribute a factor of
        [Two130]. In the field [GF], [Two130 = 5] and hence bits
        beyond the least two bits in [a4] can be seen as a wrapped
        "carry" to [a0] with a multiplicative factor of 5. We first
        give helper functions to perform these propagation.

     *)

    Definition PropagateIth (i : nat)(pf : i < 4) : code progvar.
      verse [ T0 ::= A i _ >> 32;
              A i        _ ::=& Select32;
              A (1 + i)  _ ::=+ T0
            ]%list.
    Defined.

    Definition Propagate : code progvar := iterate PropagateIth.
    Definition Wrap : code progvar :=
      [ T0 ::= a4 >> 2; a4 ::=& Select2; T0 ::=* 5 ; a0 ::=+ T0]%list.

    (** ** Adjusting [a0,..,a4] to maintain the invariant.

        After multiplication of [R] to the accumulator using the
        routine [MulR] the number of bits in all the registers
        [a0..a4] nearly doubles.  With a reduction and a carry
        propagation we can maintain this invariant. However, this
        needs to be carefully done to avoid problems.

        Propagating carries from [ai] to [ai1] makes [ai] 32-bits.
        However, as described above, the bits beyond the least two
        bits of [a4] wrap back to [a0] and results in a reduction
        modulo [Two130 - 5]. To get the bit pattern as described
        above, we should start from [a3] so that when we terminate,
        all the [a0..a3] will have 32-bits each and [a4] 3-bits (one
        more than the ideal 2-bits).

     *)

    Definition AdjustBits : code progvar.
      verse  (PropagateIth 3 _
                           ++ Wrap
                           ++ Propagate
             ).
    Defined.


    (** ** Final modular reduction.

        Let [p] be the prime [Two130 - 5], and let [alpha] be such
        that [0 <= alpha < 2p].  We would need to subtract at most a
        [p]. Let [u] denote 131-st bit of [alpha + 5] then [u = 1] if
        and only if [alpha > p]. Furthermore, if we consider [beta =
        alpha + 5u mod Two130], i.e. [beta] is [alpha + 5] with 131-st
        bit and higher bits dropped. Then we have [beta = alpha mod p]
        and that [0 <= beta < p]. This is the representation we are
        looking for.

        The proof is as follows.

        1. Note that if [alpha < p] then [alpha + 5 < Two130] and
           hence the 131-st bit is zero. Hence [alpha + 5 u = alpha]
           which is indeed the desired one.

        2. If [p <= alpha < 2p] then [Two130 <= alpha + 5 < Two131 -
           5]. Hence the bits starting from 131 is exactly 1. In this
           case [alpha + 5 = beta + Two130] and hence [alpha - Two130
           + 5 = beta], which is what we want.

     The function below computes the desired reduction amount [u].

     *)
     Definition  ReductionAmount : code progvar :=
       [ T0 ::= a0 + 5;
         T0 ::=>> 32;
         T0 ::=+ a1;
         T0 ::=>> 32;
         T0 ::=+ a2;
         T0 ::=>> 32;
         T0 ::=+ a3;
         T0 ::=>> 32;
         T0 ::=+ a4;
         T0 ::=>> 2
       ]%list.

     (** Consider the number stored in the accumulator registers
         [a0..a4]. We assume that the value that we have is the value
         available at the end of an update. As a result the value
         [alpha] inside the accumulator can at best be upper bounded
         as [alpha < Two131 - 1]. The upper bound here is slightly
         more than [2p] however a single [Wrap] step should take care.
         We can then do the full reduction as described above. We can
         optimise out the carry propagation after the [Wrap] step and
         differ it till the additional [u*5] is added (if required).
      *)

     Definition FullReduction : code progvar :=
       Wrap ++ ReductionAmount
            ++ [ T0 ::= T0 * 5; a0 ::=+ T0]
            ++ Propagate.

     (** ** Computing the hash.

         The final message has is computed using the algorithm [A + S
         mod Two128]. The elem

      *)

     Definition ComputeMAC := FullReduction ++ Add128 SArray ++ Propagate ++ StoreA.


     (** * Handling input.

      When computing the poly1305 MAC, we need to take each successive
      block of data, convert it into the appropriate coefficient of
      the message polynomial and add it to the accumulator for the
      Horner's method. We have two variants depending on whether the
      block is full or partial.
      *)

    Definition ProcessBlock (AddC : progvar Block -> code progvar)(blk : progvar Block)
      : code progvar
      := AddC blk ++ MulR ++ AdjustBits.

    Definition ProcessFullBlock : progvar Block -> code progvar  := ProcessBlock AddFullBlock.
    Definition ProcessLastBlock : progvar Block -> code progvar  := ProcessBlock Add128.

    (** * The exported functions and iterators.

        We are now ready to define all the relevant functions that a
        poly1305 implementation needs. Recall that we have two
        variants of poly1305 iterator, a partial block handling
        function and a clamping function.

     *)

    (** ** Incremental processing.

        This iterator is used to process complete blocks which forms
        the intermediate blocks of the message. Consider computing the
        message hash of a streaming input. We have with us currently
        few full blocks and more data is expected. We can use this
        iterator to process such data.

     *)

    Definition poly1305Iter : iterator Block progvar.
      verse {| setup    := LoadA  ++ LoadR;
               process  := ProcessFullBlock;
               finalise := StoreA
            |}.
    Defined.


    (** ** MAC for complete blocks.

        This iterator updates the accumulator with the message
        hash. The use case of this iterator is the following
        situation: We have already processed some blocks using the
        [poly1305Iter] and we are left with a message that is a
        multiple of the block length.

     *)

    Definition poly1305IterMAC :=
      {| setup    := setup poly1305Iter;
         process  := process poly1305Iter;
         finalise := ComputeMAC
      |}.


    (** ** Processing partial block.

        This function updates the accumulator with the message hash
        when the message is smaller than the block size but is padded
        appropriately. The use case of this function is to handle the
        last partial block.
     *)

    Definition poly1305PartialMAC : code progvar
      := setup poly1305IterMAC
               ++ ProcessLastBlock LastBlock
               ++ finalise poly1305IterMAC.


    (** ** Clamping [r].

        The parameter [r] used in Poly1305 has certain 22-bits set to
        zero. Converting an arbitrary 128-bit word to such a form is
        called clamping. The rules of clamping is the following.

        - Among the least 32-bits the top 4 bits is cleared.

        - Among the other 3 32-bits, the top 4 and the bottom 2-bits
          are cleared.

   *)

    Definition clamp (blk : progvar Block) : code progvar.
      verse [
          T0 ::= blk[- 0 -];
          T0 ::=& Ox "0f:ff:ff:fc 0f:ff:ff:ff";
          MOVE T0 TO blk[- 0 -];

          T0 ::= blk[- 1 -];
          T0 ::=& Ox "0f:ff:ff:fc 0f:ff:ff:fc";
          MOVE T0 TO blk[- 1 -]
        ]%list.
    Defined.
    Definition regClamp : Declaration := [Var T0]%vector.
    Definition clampIter : iterator Block progvar
      := {| setup    := []%list;
            process  := clamp;
            finalise := []%list
         |}.



  End Poly1305.


  Import Verse.Arch.C.

  Definition reg (regName : string) := cr uint64_t regName.

  Definition polyRegs := (- reg "a0", reg "a1", reg "a2", reg "a3", reg "a4",
                            reg "r0", reg "r1", reg "r2", reg "r3",
                            reg "p1", reg "p2", reg "p3", reg "p4",
                            reg "T0", reg "T1"
                         -).

  Definition clampReg := (- cr uint64_t "temp" -).

  Definition prototypeIncremental (fname : string) : Prototype CType + {Compile.CompileError}.
    Compile.iteratorPrototype Block fname paramsIncremental.
  Defined.
  Definition prototypeBlockMac (fname : string) : Prototype CType + {Compile.CompileError}.
    Compile.iteratorPrototype Block fname paramsBlockMac.
  Defined.
  Definition prototypePartialMac (fname : string) : Prototype CType + {Compile.CompileError}.
    Compile.functionPrototype fname paramsPartialMac.
  Defined.
  Definition prototypeClamp (fname : string) : Prototype CType + {Compile.CompileError}.
    Compile.iteratorPrototype Block fname paramsClamp.
  Defined.


  Definition implementationIncremental (fname : string) : Doc + {Compile.CompileError}.
    Compile.iterator Block fname paramsIncremental Empty register.
    assignRegisters polyRegs.
    statements poly1305Iter.
  Defined.

  Definition implementationBlockMac (fname : string) : Doc + {Compile.CompileError}.
    Compile.iterator Block fname paramsBlockMac Empty register.
    assignRegisters polyRegs.
    statements poly1305IterMAC.
  Defined.

  Definition implementationPartialMac (fname : string) : Doc + {Compile.CompileError}.
    Compile.function fname paramsPartialMac Empty register.
    assignRegisters polyRegs.
    statements poly1305PartialMAC.
  Defined.

  Definition implementationClamp (fname : string) : Doc + {Compile.CompileError}.
    Compile.iterator Block fname Empty Empty regClamp.
    assignRegisters clampReg.
    statements clampIter.
  Defined.


  Definition incrementalName (fname : string) := fname ++ "_incremental".
  Definition blockMacName    (fname : string) := fname ++ "_blockmac".
  Definition partialMacName(fname : string)    := fname ++ "_partialmac".
  Definition clampName       (fname : string) := fname ++ "_clamp".

  Definition implementation (fname : string) : Doc + {Compile.CompileError} :=
    incr <- implementationIncremental (incrementalName  fname) ;
      blockmac <- implementationBlockMac (blockMacName fname) ;
      partialmac <- implementationPartialMac (partialMacName fname);
      clamp <- implementationClamp (clampName fname);
      {- vcat [ incr; blockmac; partialmac; clamp ]%list -}.


  Definition prototypes fname :=
    incrP <- prototypeIncremental (incrementalName fname);
      blockmacP <- prototypeBlockMac (blockMacName fname);
      partialmacP <- prototypePartialMac (partialMacName fname);
      clampP <- prototypeClamp (clampName fname);
      {- [ incrP; blockmacP; partialmacP; clampP]%list -}.

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
