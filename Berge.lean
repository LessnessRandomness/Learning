import Mathlib.Init.Function
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card

def IsMaximum {V} {G: SimpleGraph V} {M: G.Subgraph} (_: M.IsMatching): Prop :=
  ∀ (M': G.Subgraph), M'.IsMatching → M'.support.ncard ≤ M.support.ncard

def AlternatingWalk {V} {G: SimpleGraph V} (M: G.Subgraph) {x y: V} (b: Bool) (W: G.Walk x y): Prop :=
  match b, W with
  | _, SimpleGraph.Walk.nil => True
  | true, @SimpleGraph.Walk.cons _ _ x' y' _ _ p => M.Adj x' y' ∧ AlternatingWalk M false p
  | false, @SimpleGraph.Walk.cons _ _ x' y' _ _ p => ¬ M.Adj x' y' ∧ AlternatingWalk M true p

def AugmentingPath {V} {G: SimpleGraph V} (M: G.Subgraph) {x y: V} (P: G.Path x y): Prop :=
  x ∉ M.support ∧ y ∉ M.support ∧ AlternatingWalk M false P.val



def XOR (P1 P2: Prop): Prop := P1 ∧ ¬ P2 ∨ ¬ P1 ∧ P2

theorem aux {V} {G: SimpleGraph V} (M: G.Subgraph): ∀ (x y: V), M.Adj x y → G.Adj x y := by
  induction M
  simp
  assumption

def GraphSymmDiff {V} {G: SimpleGraph V} (M1 M2: G.Subgraph): G.Subgraph :=
  SimpleGraph.Subgraph.mk
  (@Set.univ V)
  (fun x y => XOR (M1.Adj x y) (M2.Adj x y))
  (by
    intros x y H
    simp [XOR] at H
    let W1 := aux M1 x y
    let W2 := aux M2 x y
    tauto)
  (by
    intros x y H
    simp)
  (by
    simp [Symmetric, XOR]
    intros x y H
    tauto)



theorem Berge's_lemma {V} [Finite V] {G: SimpleGraph V} {M: SimpleGraph.Subgraph G} (H: M.IsMatching):
  IsMaximum H ↔ (∀ (x y: V) (P: SimpleGraph.Path G x y), ¬ AugmentingPath M P) := by
  sorry
