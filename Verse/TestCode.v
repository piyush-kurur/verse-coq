Require Import Verse.Error.
Require Import Verse.Arch.C.
Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Language.
Require Import Verse.Syntax.
Require Import Verse.PrettyPrint.
Require Import Verse.Word.

Require Import String.
Require Import List.
Import ListNotations.



Section TestFunction.

  Variable variable : varT.
  (* The parameters of the function *)
  Variable arr     : variable (ArrayT 5 hostE Word16).
  Variable A B     : variable Byte.
  (* The local variables *)
  Variable num      : variable Word16.
  (* The temp register *)
  Variable tmp       : variable Word16.

  Definition testFunction : list (instruction variable) :=
    [ num <= tmp [+] Ox "abcd";
      A   <= A [+] B;
      num <= tmp [-] num ;
      num      <= tmp      [*] arr[-1-];
      num      <= arr[-1-] [/] tmp ;
      arr[-1-] <= tmp      [|] num ;
      num      <= tmp      [&] arr[-1-];
      num      <= tmp      [^] num ;
      (* binary update *)
      num <=+ tmp;
      num <=- arr[-1-];
      num <=* Ox "1234";
      num <=/ tmp;
      num <=| tmp;
      num <=& tmp;
      num <=^ tmp;
      
      (* Unary operators *)
      num      <=~ tmp;
      tmp      <=  arr[-1-] <<  42;
      tmp      <=  arr[-1-] >>  42;
      num      <=  tmp     <*< 42;
      arr[-1-] <=  tmp     >*> 42;
      
      (* Unary update operators *)
      tmp      <=<<  (42%nat);
      tmp      <=>>  (42%nat);
      num      <=<*< (42%nat);
      arr[-1-] <=>*> (42%nat)
    ].
      
End TestFunction.

Definition regVars : allocation C.register [Word16] := (cr Word16 "temp", tt). 
Definition code := CompileC.compile "testFunction" [ArrayT 5 hostE Word16; Byte; Byte] [Word16] regVars testFunction.

Compute (recover (layout <$> code)).
