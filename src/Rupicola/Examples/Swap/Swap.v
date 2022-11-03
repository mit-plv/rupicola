Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.Syntax. Import Syntax.Coercions.
Require Import bedrock2.NotationsCustomEntry.
Require bedrock2.WeakestPrecondition.
Local Open Scope Z_scope. Local Open Scope string_scope.
Import ListNotations.

Module Bedrock2.
  Definition swap := func! (a, b) {
       tmp = ( load( a ) ) ;
       store( a, load( b ) );
       store( b, tmp )}.
End Bedrock2.
