From Coq Require Import ssreflect Program FunInd Lia.

From Binary.Util Require Import Notation.
From Binary.Structure Require Import Binary.
From Binary.Data Require Import Bit Octett.

Module Bin := Binary.
Module Oct := Octett.

Import Bin.Notations.

Module ByteVec.

  Notation Octett := Oct.Octett.
  Notation Bit := Bit.Bit.

  Inductive ByteVec : nat -> Type :=
  | nil           : ByteVec 0
  | cons `{l : nat} : Octett -> ByteVec l -> ByteVec $ S l.

  Definition hd `{n : nat} (v : ByteVec $ S n) : Octett    := let 'cons hd _ := v in hd.
  Definition tl `{n : nat} (v : ByteVec $ S n) : ByteVec n := let 'cons _ tl := v in tl.

  Program Fixpoint nth_byte `{l : nat} (v : ByteVec $ S l) (n : nat) (H : n < S l) : Octett :=
    match n as k return k = n -> n < S l -> Octett with
    | 0    => fun _ _ => hd v
    | S n' => fun Hk H =>
      match l as m return l = m -> Octett with
      | 0 => fun _ => False_rect Octett _
      | S l' => fun Hm => let v' : ByteVec $ S (S l') := eq_rect _ _ v _ _ in
                      @nth_byte l' (tl v') n' _
      end _
    end _ H.
  Solve Obligations with abstract lia.

  Notation Byte  := (ByteVec 1).
  Notation Word  := (ByteVec 2).
  Notation DWord := (ByteVec 4).
  Notation QWord := (ByteVec 8).
  Notation OWord := (ByteVec 16).

  Fixpoint repeat (l : nat) (o : Octett) : ByteVec l :=
    match l with
    | 0   => nil
    | S l => cons o $ repeat l o
    end.

  Fixpoint map `{l : nat} (v : ByteVec l) (f : Octett -> Octett) :=
    match v with
    | nil => nil
    | cons hd tl => cons (f hd) (map tl f)
    end.

  Fixpoint map2 `{l : nat} (v1 v2 : ByteVec l) (f : Octett -> Octett -> Octett) :=
    match v1 in ByteVec l return ByteVec l -> ByteVec l with
    | nil          => fun _  => nil
    | cons hd1 tl1 => fun v2 => let hd2 := hd v2 in
                            let tl2 := tl v2 in
                            cons (f hd1 hd2) (map2 tl1 tl2 f)
    end v2.

  Fixpoint map3 `{l : nat} (v1 v2 v3 : ByteVec l) (f : Octett -> Octett -> Octett -> Octett) :=
    match v1 in ByteVec l return ByteVec l -> ByteVec l -> ByteVec l with
    | nil          => fun _  _ => nil
    | cons hd1 tl1 => fun v2 v3 => let hd2 := hd v2 in
                            let tl2 := tl v2 in
                            let hd3 := hd v3 in
                            let tl3 := tl v3 in
                            cons (f hd1 hd2 hd3) (map3 tl1 tl2 tl3 f)
    end v2 v3.

  Definition all_zero n := repeat n Oct.all_zero.
  Definition all_one  n := repeat n Oct.all_one.

  Definition inv `{l : nat} (v : ByteVec l) := map v Oct.inv.

  Definition and `{l : nat} (v1 v2 : ByteVec l) := map2 v1 v2 Oct.and.
  Definition  or `{l : nat} (v1 v2 : ByteVec l) := map2 v1 v2 Oct.or.

  Fixpoint shl `{l : nat} (v : ByteVec l) (b : Bit) : (Bit * ByteVec l) :=
    match v with
    | nil => (Bit.Zero, nil)
    | cons hd tl =>
        let '(b__tl, tl') := shl tl b in
        let '(b__hd, hd') := Oct.shl hd b__tl in
        (b__hd, cons hd' tl')
    end.

  Fixpoint shr `{l : nat} (v : ByteVec l) (b : Bit) : (Bit * ByteVec l) :=
    match v with
    | nil => (Bit.Zero, nil)
    | cons hd tl =>
        let '(b__hd, hd') := Oct.shr hd b in
        let '(b__tl, tl') := shr tl b__hd in
        (b__tl, cons hd' tl')
    end.

  Definition masked_set `{l : nat} (dst src mask : ByteVec l) :=
    map3 dst src mask Oct.masked_set.

End ByteVec.
