(* -------------------------------------------------------------------- *)
(* -------- *) Require Import PArray Uint63.
From Bignums   Require Import BigN BigZ BigQ.
From BinReader Require Import BinReader.

(* -------------------------------------------------------------------- *)
Time LoadData "tests/tests.bin" As data.

(* -------------------------------------------------------------------- *)
Eval compute in data.
