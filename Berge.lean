import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card


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

def SimpleGraph.Subgraph.SymmDiff {V} {G: SimpleGraph V} (M1 M2: G.Subgraph): G.Subgraph :=
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
    intros x _ _
    simp)
  (by
    simp [Symmetric, XOR]
    intros x y H
    tauto)

theorem aux0 {V} {G: SimpleGraph V} {M1 M2: G.Subgraph} (H1: M1.IsMatching) (H2: M2.IsMatching):
  let S := M1.SymmDiff M2
  ∀ (x: V), x ∈ S.verts → (S.neighborSet x).encard ≤ 2 := by
    simp
    simp [SimpleGraph.Subgraph.SymmDiff]
    simp [SimpleGraph.Subgraph.neighborSet]
    simp [XOR]
    intro x
    simp [SimpleGraph.Subgraph.IsMatching] at H1
    simp [SimpleGraph.Subgraph.IsMatching] at H2
    set S1 := { w | M1.Adj x w ∧ ¬ M2.Adj x w }
    set S2 := { w | ¬ M1.Adj x w ∧ M2.Adj x w }
    have H3: { w | M1.Adj x w ∧ ¬ M2.Adj x w ∨ ¬ M1.Adj x w ∧ M2.Adj x w} = S1 ∪ S2 := by trivial
    have H4: Disjoint S1 S2 := by
      simp
      simp [Disjoint]
      intros x_1 H4 H5 x_2 H6
      simp
      set T1 := H4 H6
      set T2 := H5 H6
      simp at T1
      simp at T2
      tauto
    rewrite [H3]
    rewrite [Set.encard_union_eq H4]
    clear H3
    set T1 := { w | M1.Adj x w }
    set T2 := { w | M2.Adj x w }
    have H5: S1 = T1 \ T2 := by trivial
    have H6: S2 = T2 \ T1 := by
      rewrite [Set.ext_iff]
      intro x0
      simp
      tauto
    have H7: S1.encard ≤ T1.encard := by
      apply Set.encard_le_of_subset
      intros x_1
      rewrite [H5]
      simp
      tauto
    have H8: S2.encard ≤ T2.encard := by
      apply Set.encard_le_of_subset
      intros x_1
      rewrite [H6]
      simp
      tauto
    have H9: Set.encard T1 <= 1 := by
      clear H7 H6 H5
      revert T1
      simp
      cases (em (x ∈ M1.verts)) with
      | inl h => have HH: Set.encard { w | M1.Adj x w } = 1 := by
                   set H9 := H1 h
                   rewrite [Set.encard_eq_one]
                   cases H9 with | intro w h0 =>
                   cases h0 with | intro left right =>
                   simp at right
                   exists w
                   cases H9 with | intro w0 h1 =>
                   simp at h1
                   cases h1 with | intro left0 right0 =>
                   rewrite [Set.ext_iff]
                   intros x2
                   simp
                   constructor
                   . tauto
                   . intro H10
                     rewrite [H10]
                     assumption
                 rewrite [HH]
                 trivial
      | inr h => have HH: { w | M1.Adj x w} = ∅ := by
                   rewrite [Set.ext_iff]
                   simp
                   intros x_1 H9
                   apply h
                   induction M1 with | mk verts Adj adj_sub edge_vert symm =>
                   simp at H9
                   simp
                   apply edge_vert
                   exact H9
                 rewrite [HH]
                 simp
    have H10: Set.encard T2 <= 1 := by
      clear H6 H8 H5
      revert T2
      simp
      cases (em (x ∈ M2.verts)) with
      | inl h => have HH: Set.encard { w | M2.Adj x w } = 1 := by
                   set H9 := H2 h
                   rewrite [Set.encard_eq_one]
                   cases H9 with | intro w h0 =>
                   cases h0 with | intro left right =>
                   simp at right
                   exists w
                   cases H9 with | intro w0 h1 =>
                   simp at h1
                   cases h1 with | intro left0 right0 =>
                   rewrite [Set.ext_iff]
                   intros x2
                   simp
                   constructor
                   . tauto
                   . intro H10
                     rewrite [H10]
                     assumption
                 rewrite [HH]
                 trivial
      | inr h => have HH: { w | M2.Adj x w } = ∅ := by
                   rewrite [Set.ext_iff]
                   simp
                   intros x_1 H9
                   apply h
                   induction M2 with | mk verts Adj adj_sub edge_vert symm =>
                   simp at H9
                   simp
                   apply edge_vert
                   exact H9
                 rewrite [HH]
                 simp
    apply (add_le_add H7 H8).trans
    apply (add_le_add H9 H10)

theorem encard_aux0 {V} (S: Set V) (H: S.encard ≤ 2):
  S.encard = 0 ∨ S.encard = 1 ∨ S.encard = 2 := by
  set H0 := @Set.encard_le_coe_iff _ S 2
  simp at H0
  cases H0 with | intro mp mpr =>
  set H1 := mp H
  clear mpr H0
  cases H1 with | intro left right =>
  cases right with | intro w h =>
  cases h with | intro left0 right0 =>
  have H2: w = 0 ∨  w = 1 ∨ w = 2 := by
    cases w with
    | zero => tauto
    | succ n => cases n with
                | zero => tauto
                | succ n => cases n with
                            | zero => tauto
                            | succ n => simp
                                        trivial
  cases H2 with
  | inl h => rewrite [h] at left0
             simp at left0
             rewrite [left0]
             simp
  | inr h => cases h with
             | inl h => rewrite [h] at left0
                        simp at left0
                        tauto
             | inr h => rewrite [h] at left0
                        simp at left0
                        tauto

theorem aux1 {V} [F: Fintype V] [D: DecidableEq V] {G: SimpleGraph V} (M: G.Subgraph):
  (∀ (x: V), x ∈ M.verts → (M.neighborSet x).encard ≤ 2) →
  ∀ (c: M.coe.ConnectedComponent),
  ∃ (x y: V) (W: G.Walk x y), W.IsTrail ∧ W.toSubgraph = (⊤: G.Subgraph).induce c.supp := by
    intros H

    sorry

/- maybe to remove later, dunno -/
theorem aux3 {V} {G: SimpleGraph V} {M1 M2: G.Subgraph} (H1: M1.IsMatching) (H2: M2.IsMatching):
  ∀ (c: (M1.SymmDiff M2).coe.ConnectedComponent),
  (∃ (x: V), ∀ (y: V), Set.Mem y c.supp → x = y) ∨
  (∃ (x: V) (W: G.Walk x x) (b: Bool), W.IsCycle ∧ AlternatingWalk M1 M2 b W ∧ W.toSubgraph = (⊤: G.Subgraph).induce c.supp) ∨ /- some black magic, uff -/
  (∃ (x y: V) (W: G.Walk x y) (b: Bool), x ≠ y ∧ W.IsPath ∧ AlternatingWalk M1 M2 b W ∧ W.toSubgraph = (⊤: G.Subgraph).induce c.supp) /- same thing here too -/
  := by
    intros c
    sorry

theorem Berge's_lemma {V} [F: Fintype V] [D: DecidableEq V] {G: SimpleGraph V} {M: SimpleGraph.Subgraph G} (H: M.IsMatching):
  IsMaximum H ↔ (∀ (x y: V) (P: SimpleGraph.Path G x y) (b: Bool), ¬ AugmentingPath M P) := by

  sorry
