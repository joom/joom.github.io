/-
Checked with QPFTypes commit 5b5dd4f83121662838b99d129b92f632f263c508
and its pinned Lean 4.25.0 toolchain.

Run from that QPFTypes checkout:

  lake env lean BadCoinduction.lean
-/

import Qpf

set_option linter.unusedVariables false
set_option linter.unreachableTactic false

codata Colist α where
  | conil : Colist α
  | cocons : α → Colist α → Colist α

codata Cotree α where
  | node : α → Colist (Cotree α) → Cotree α

namespace Colist

def head? (xs : Colist α) : Option α :=
  match MvQPF.Cofix.dest xs with
  | .conil => none
  | .cocons value _ => some value

def tail? (xs : Colist α) : Option (Colist α) :=
  match MvQPF.Cofix.dest xs with
  | .conil => none
  | .cocons _ tail => some tail

def map (f : α → β) : Colist α → Colist β :=
  MvQPF.Cofix.corec (fun xs =>
    match MvQPF.Cofix.dest xs with
    | .conil => Shape.conil
    | .cocons value tail => Shape.cocons (f value) tail)

def eqPrefix [BEq α] : Nat → Colist α → Colist α → Bool
  | 0, _, _ => true
  | n + 1, xs, ys =>
      match MvQPF.Cofix.dest xs, MvQPF.Cofix.dest ys with
      | .conil, .conil => true
      | .cocons (x : α) xs, .cocons (y : α) ys =>
          (x == y) && eqPrefix n xs ys
      | _, _ => false

example : head? (Colist.conil : Colist α) = none := by
  rfl

example (value : α) (tail : Colist α) :
    head? (Colist.cocons value tail) = some value := by
  rfl

example (f : α → β) :
    head? (map f Colist.conil) = none := by
  rfl

example (f : α → β) (value : α) (tail : Colist α) :
    head? (map f (Colist.cocons value tail)) = some (f value) := by
  rfl

/- This tail equation is not definitional. -/

example (f : α → β) (value : α) (tail : Colist α) : True := by
  fail_if_success
    have :
        tail? (map f (Colist.cocons value tail)) =
          some (map f tail) := by
      rfl
  trivial

/- Extensional equality is not proved by `rfl`. -/

example (xs : Colist α) : True := by
  fail_if_success
    have : map id xs = xs := by
      rfl
  trivial

end Colist

namespace Cotree

def root (tree : Cotree α) : α :=
  match MvQPF.Cofix.dest tree with
  | .node value _ => value

def children (tree : Cotree α) : Colist (Cotree α) :=
  match MvQPF.Cofix.dest tree with
  | .node _ children => children

def map (f : α → β) : Cotree α → Cotree β :=
  MvQPF.Cofix.corec (fun tree =>
    match MvQPF.Cofix.dest tree with
    | .node value children => Shape.node (f value) children)

def unfold (next : α → Colist α) : α → Cotree α :=
  MvQPF.Cofix.corec (fun initial =>
    Shape.node initial (next initial))

def rootAndFirstChild? (tree : Cotree α) : Option (α × α) :=
  match MvQPF.Cofix.dest tree with
  | .node root children =>
      match MvQPF.Cofix.dest children with
      | .conil => none
      | .cocons child _ =>
          match MvQPF.Cofix.dest child with
          | .node childRoot _ => some (root, childRoot)

example (value : α) (children : Colist (Cotree α)) :
    root (Cotree.node value children) = value := by
  rfl

example (f : α → β) (value : α) (children : Colist (Cotree α)) :
    root (map f (Cotree.node value children)) = f value := by
  rfl

/- This children equation is not definitional. -/

example (f : α → β) (value : α)
    (children : Colist (Cotree α)) : True := by
  fail_if_success
    have :
        Cotree.children (map f (Cotree.node value children)) =
          Colist.map (map f) children := by
      rfl
  trivial

/- Extensional equality is not proved by `rfl`. -/

example (tree : Cotree α) : True := by
  fail_if_success
    have : map id tree = tree := by
      rfl
  trivial

example (next : α → Colist α) (initial : α) :
    root (unfold next initial) = initial := by
  rfl

/- The recursive unfold equation is not definitional. -/

example (next : α → Colist α) (initial : α) : True := by
  fail_if_success
    have :
        children (unfold next initial) =
          Colist.map (unfold next) (next initial) := by
      rfl
  trivial

end Cotree

/- A declaration with no live parameter is rejected. -/

/--
error: Due to a bug, codatatype without any parameters don't quite work yet. Please try adding parameters to your type
-/
#guard_msgs in
codata BadNoParameter where
  | loop : BadNoParameter

/- A mutual codata block is rejected by Lean's mutual block checker. -/

/--
error: invalid mutual block: either all elements of the block must be inductive/structure declarations, or they must all be definitions/theorems/abbrevs
-/
#guard_msgs in
mutual
  codata MutualRose α where
    | node : α → MutualForest α → MutualRose α

  codata MutualForest α where
    | nil : MutualForest α
    | cons : MutualRose α → MutualForest α → MutualForest α
end

/- An indexed family is rejected by `codata`. -/

/--
error: Unexpected type; type will be automatically inferred. Note that inductive families are not supported due to inherent limitations of QPFs
-/
#guard_msgs in
codata IndexedStream α : Nat → Type where
  | mk : α → IndexedStream α (n + 1) → IndexedStream α n
