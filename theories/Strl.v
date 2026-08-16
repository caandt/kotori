From Stdlib Require Import List Uint63 PString Recdef Lia ZifyUint63 ZArith Utf8.
Open Scope uint63.
Open Scope pstring.

Module SL.
  Fixpoint get sl i :=
    match sl with
    | nil => 0
    | a::t =>
        if (i <? length a)
        then PrimString.get a i
        else get t (i - length a)
    end.
  Definition cat := @app string.
  Fixpoint sub sl i n :=
    if (n =? 0) then nil else
    match sl with
    | nil => nil
    | a::t =>
        if (i <? length a) then
          let x := PrimString.sub a i n in
          x::sub t 0 (n - length x)
        else
          sub t (i - length a) n
    end.
  Definition length sl := List.fold_left add (map length sl) 0.
  Fixpoint drop sl n :=
    if (n =? 0) then sl else
    match sl with
    | nil => nil
    | a::t =>
        if (n <? PrimString.length a) then
          PrimString.sub a n (PrimString.length a)::t
        else
          drop t (n - PrimString.length a)
    end.
  Fixpoint llt sl n :=
    if (n =? 0) then false else
    match sl with
    | nil => true
    | a::t =>
        if (n <? PrimString.length a) then false
        else llt t (n - PrimString.length a)
    end.
  Definition splice sl i sl2 :=
    cat (cat (sub sl 0 i) sl2) (drop sl (i + length sl2)).
End SL.
Import SL.
Definition list_of_strl sl := List.concat (map to_list sl).
Notation "'LO'" := list_of_strl.
Notation equiv sl1 sl2 := (list_of_strl sl1 = list_of_strl sl2).
Infix "≡" := equiv.
