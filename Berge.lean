import Mathlib.Init.Function
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card
import Mathlib.Order.SymmDiff


def SimpleGraph.Subgraph.Complement {V} (G: SimpleGraph V) (M: G.Subgraph): G.Subgraph :=
  SimpleGraph.Subgraph.mk
    (@Set.univ V)
    (fun x y => G.Adj x y ∧ ¬ M.Adj x y)
    (by
      tauto)
    (by
      tauto)
    (by
      intros x y H
      tauto)

-- Fintype ↑(SimpleGraph.Subgraph.support M')

def IsMaximum {V} {G: SimpleGraph V} {M: G.Subgraph} (_: M.IsMatching): Prop :=
  ∀ (M': G.Subgraph) (_: M'.IsMatching),
  M'.support.encard ≤ M.support.encard

def AlternatingWalk {V} {G: SimpleGraph V} (M1 M2: G.Subgraph) {x y: V} (b: Bool) (W: G.Walk x y): Prop :=
  match b, W with
  | _, SimpleGraph.Walk.nil => True
  | true, @SimpleGraph.Walk.cons _ _ x' y' _ _ p => M1.Adj x' y' ∧ AlternatingWalk M1 M2 false p
  | false, @SimpleGraph.Walk.cons _ _ x' y' _ _ p => M2.Adj x' y' ∧ AlternatingWalk M1 M2 true p

def AugmentingPath {V} {G: SimpleGraph V} (M: G.Subgraph) {x y: V} (P: G.Path x y): Prop :=
  x ∉ M.support ∧ y ∉ M.support ∧ AlternatingWalk M M.Complement false P.val


def XOR (P1 P2: Prop): Prop := P1 ∧ ¬ P2 ∨ ¬ P1 ∧ P2

def GraphSymmDiff {V} {G: SimpleGraph V} (M1 M2: G.Subgraph): G.Subgraph :=
  SimpleGraph.Subgraph.mk
  (@Set.univ V)
  (fun x y => XOR (M1.Adj x y) (M2.Adj x y))
  (by
    intros x y H
    simp [XOR] at H
    set W1 := M1.adj_sub (v:=x) (w:=y)
    set W2 := M2.adj_sub (v:=x) (w:=y)
    tauto)
  (by
    intros x y H
    simp)
  (by
    simp [Symmetric, XOR]
    intros x y H
    tauto)

def aux0 {V} {G: SimpleGraph V} {M1 M2: G.Subgraph} (H1: M1.IsMatching) (H2: M2.IsMatching):
  let S := GraphSymmDiff M1 M2
  ∀ (x: V), x ∈ S.verts → (S.neighborSet x).encard ≤ 2 := by
    sorry

/- Is this correct? Does it corresponds to lemma from https://en.wikipedia.org/wiki/Berge%27s_theorem#Proof ? -/
theorem aux1 {V} {G: SimpleGraph V} {M1 M2: G.Subgraph} (H1: M1.IsMatching) (H2: M2.IsMatching):
  ∀ (c: (GraphSymmDiff M1 M2).coe.ConnectedComponent),
  (∃ (x: V), ∀ (y: V), Set.Mem y c.supp → x = y) ∨
  (∃ (x: V) (W: G.Walk x x) (b: Bool), W.IsCycle ∧ AlternatingWalk M1 M2 b W ∧ W.toSubgraph = (⊤: G.Subgraph).induce c.supp) ∨ /- some black magic, uff -/
  (∃ (x y: V) (W: G.Walk x y) (b: Bool), x ≠ y ∧ W.IsPath ∧ AlternatingWalk M1 M2 b W ∧ W.toSubgraph = (⊤: G.Subgraph).induce c.supp) /- same thing here too -/
  := by
  sorry

theorem Berge's_lemma {V} [Finite V] {G: SimpleGraph V} {M: SimpleGraph.Subgraph G} (H: M.IsMatching):
  IsMaximum H ↔ (∀ (x y: V) (P: SimpleGraph.Path G x y) (b: Bool), ¬ AugmentingPath M P) := by
  sorry
