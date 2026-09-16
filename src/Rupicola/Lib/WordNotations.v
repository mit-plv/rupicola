Require Import Rupicola.Lib.Core.

Declare Scope word.
Notation "~w w" := (Zmod.not w) (at level 30, no associativity): word.
Infix "*w" := Zmod.mul (at level 40, left associativity): word.
Infix "/w" := Zmod.udiv (at level 40, left associativity): word.
Infix "/sw" := Zmod.squot (at level 40, left associativity): word.
Infix "+w" := Zmod.add (at level 50, left associativity): word.
Infix "-w" := Zmod.sub (at level 50, left associativity): word.
Infix ">>w" := Semantics.sru (at level 60, no associativity): word.
Infix ">>>w" := Semantics.srs (at level 60, no associativity): word.
Infix "<<w" := Semantics.slu (at level 60, no associativity): word.
Notation "w1 <w w2" := (word.b2w (Semantics.ltu w1 w2)) (at level 70, no associativity): word.
Notation "w1 >w w2" := (word.b2w (Semantics.ltu w2 w1)) (at level 70, no associativity): word.
Notation "w1 <sw w2" := (word.b2w (Semantics.lts w1 w2)) (at level 70, no associativity): word.
Notation "w1 >sw w2" := (word.b2w (Semantics.lts w2 w1)) (at level 70, no associativity): word.
Notation "w1 ==w w2" := (word.b2w (Zmod.eqb w1 w2)) (at level 80, no associativity): word.
Infix "&w" := Zmod.and (at level 90, left associativity): word.
Infix "^w" := Zmod.xor (at level 92, left associativity): word.
Infix "|w" := Zmod.or (at level 94, left associativity): word.

Open Scope word.
