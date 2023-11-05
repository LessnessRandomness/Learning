import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.Subgraph
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
    interval_cases w
    . trivial
    . trivial
    . trivial
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

theorem encard_aux1 {V} (S: Set V) (H: S.encard ≤ 2):
  S = ∅ ∨ (∃ x, S = {x}) ∨ (∃ x y, x ≠ y ∧ S = {x, y}) := by
    set H0 := encard_aux0 S H
    cases H0 with
    | inl h => set H1 := (@Set.encard_eq_zero _ S)
               tauto
    | inr h => cases h with
               | inl h => set H1 := (@Set.encard_eq_one _ S)
                          right
                          left
                          tauto
               | inr h => set H1 := (@Set.encard_eq_two _ S)
                          right
                          right
                          tauto

theorem aux1_subcase_1 {V} {G: SimpleGraph V} (M: G.Subgraph):
  ∀ (x: V) (H: x ∈ M.verts), M.neighborSet x = ∅ →
  ∃ (W: G.Walk x x), W.IsTrail ∧
  W.toSubgraph = M.induce (M.coe.connectedComponentMk ⟨x, H⟩).supp := by
    intros v H H0
    exists SimpleGraph.Walk.nil (u := v)
    apply And.intro
    . simp
    . simp
      rewrite [Set.ext_iff] at H0
      simp at H0
      simp [SimpleGraph.Subgraph.induce]
      simp [SimpleGraph.singletonSubgraph]
      apply And.intro
      . rewrite [Set.ext_iff]
        intros x
        simp
        apply Iff.intro
        . intro H0
          subst H0
          simp [SimpleGraph.ConnectedComponent.supp]
          simp [Lean.Internal.coeM]
          simp [SimpleGraph.Subgraph.coe]
          exists x, H
        . intro H0
          simp [SimpleGraph.ConnectedComponent.supp] at H0
          simp [Lean.Internal.coeM] at H0
          cases H0 with | intro w h0 =>
          cases h0 with | intro w0 h1 =>
          cases h1 with | intro left right =>
          simp [CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe] at right
          subst right
          simp [SimpleGraph.Reachable] at left
          cases left with | intro val =>
          set W := val.reverse
          cases W with
          | nil => simp
          | @cons _ w1 _ h' p' => exfalso
                                  apply (H0 w1)
                                  simp [SimpleGraph.Subgraph.coe] at h'
                                  assumption
      . simp [SimpleGraph.Subgraph.coe]
        simp [SimpleGraph.ConnectedComponent.supp]
        apply funext
        intros x
        apply funext
        intros x_1
        simp
        apply Iff.intro
        . tauto
        . simp [Lean.Internal.coeM]
          intros x_2 h_2 H1 H2 x_3 h_3 H3 H4 H5
          simp [CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe] at H2
          simp [CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe] at H4
          subst H2
          subst H4
          have H2: x ≠ x_1 := by
            cases M with | mk verts Adj adj_sub edge_vert symm =>
            simp at *
            cases G with | mk Adj0 symm0 loopless =>
            simp [Irreflexive] at loopless
            intros H2
            subst H2
            simp at adj_sub
            set H4 := adj_sub H5
            tauto
          have H4: x ≠ v ∨ x_1 ≠ v := by
            have H5: x ≠ v ∨ x = v := by tauto
            have H6: x_1 ≠ v ∨ x_1 = v := by tauto
            cases H5 with
            | inl h_4 => tauto
            | inr h_4 => subst h_4
                         tauto
          cases H4 with
          | inl h_4 => simp [SimpleGraph.Reachable] at H1
                       cases H1 with | intro val =>
                       set W := val.reverse
                       cases W with
                       | nil => simp at *
                       | @cons _ w1 _ h' p' => simp at h'
                                               tauto
          | inr h_4 => simp [SimpleGraph.Reachable] at H3
                       cases H3 with | intro val =>
                       set W := val.reverse
                       cases W with
                       | nil => simp at *
                       | @cons _ w1 _ h' p' => simp at h'
                                               tauto


theorem aux_experiment {V} [F: Fintype V] [I: Inhabited V] {G: SimpleGraph V} (M: G.Subgraph):
  (∀ (x: V), x ∈ M.verts → (M.neighborSet x).encard ≤ 2) →
  ∀ (c: M.coe.ConnectedComponent),
  ∃ (x y: V) (W: G.Walk x y), W.IsTrail ∧ W.toSubgraph = M.induce c.supp := by
    intros H c
    have H0: ∀ x, x ∈ M.verts →
            M.neighborSet x = ∅ ∨
            (∃ y, M.neighborSet x = {y}) ∨
            (∃ y z, y ≠ z ∧ M.neighborSet x = {y, z}) := by
      intros x H0
      apply encard_aux1
      apply H
      assumption
    clear H
    have H1: ∃ (n: Nat), M.verts.encard = ↑(n + 1) := by
      sorry
    cases H1 with | intro N H1 =>
    revert M
    induction N with
    | zero => intros M c H0 H1
              simp at H1
              rewrite [Set.encard_eq_one] at H1
              cases H1 with | intro x H1 =>
              exists x, x, SimpleGraph.Walk.nil (u := x)
              apply And.intro
              . simp
              . simp
                clear H0
                apply SimpleGraph.Subgraph.ext
                . simp
                  simp [SimpleGraph.Subgraph.coe] at c
                  cases M with | mk verts Adj adj_sub edge_vert symm =>
                  simp at H1
                  simp at c
                  subst H1
                  rewrite [Set.ext_iff]
                  simp
                  intros x_1
                  apply Iff.intro
                  . intros H1
                    subst H1
                    simp [Lean.Internal.coeM]
                    apply And.intro
                    . apply SimpleGraph.ConnectedComponent.ind
                      simp
                      intros x H1
                      subst H1
                      simp [SimpleGraph.Subgraph.coe]
                    . rfl
                  . intros H0
                    simp [SimpleGraph.ConnectedComponent.supp] at H0
                    simp [SimpleGraph.Subgraph.coe] at H0
                    simp [Lean.Internal.coeM] at H0
                    cases H0 with | intro left right =>
                    exact right
                . cases M with | mk verts Adj adj_sub edge_vert symm =>
                  simp at c
                  simp at H1
                  simp
                  subst H1
                  simp [SimpleGraph.singletonSubgraph]
                  simp [SimpleGraph.Subgraph.induce]
                  apply funext
                  intro x_1
                  apply funext
                  intro x_2
                  simp
                  apply Iff.intro
                  . tauto
                  . simp [Lean.Internal.coeM]
                    intros H0 H1 H2 H3
                    have H4: x_1 = x := by
                      exact H1
                    have H5: x_2 = x := by
                      exact H3
                    subst H4
                    subst H5
                    clear H1 H3 H0 H2
                    intros H0
                    cases G with | mk Adj' symm' loopless =>
                    simp [Irreflexive] at loopless
                    simp at adj_sub
                    exact (loopless _ (adj_sub H0))
    | succ n ih => intros M
                   apply SimpleGraph.ConnectedComponent.ind
                   intros v H0 H1
                   have H3: M = M.induce ((M.deleteVerts {↑v}).verts ∪ {↑v}) := by
                     apply SimpleGraph.Subgraph.ext
                     . simp
                     . apply funext
                       intros x_1
                       apply funext
                       intros x_2
                       simp
                   set Mp: G.Subgraph := M.deleteVerts {↑v}
                   have MpH: ∀ x, x ∈ Mp.verts →
                            SimpleGraph.Subgraph.neighborSet Mp x = ∅ ∨
                            (∃ y, SimpleGraph.Subgraph.neighborSet Mp x = {y}) ∨
                            (∃ y z, y ≠ z ∧ SimpleGraph.Subgraph.neighborSet Mp x = {y, z}) := by
                     clear ih
                     intros x Hx
                     simp at Hx
                     simp
                     cases Hx with | intro Hx H4 =>
                     set H5 := H0 x Hx
                     cases H5 with
                     | inl H6 => clear H5
                                 left
                                 rewrite [Set.ext_iff] at H6
                                 rewrite [Set.ext_iff]
                                 simp at H6
                                 simp
                                 intros x_1 H7 H8 Hx_1 H9 H10
                                 apply H6
                                 exact H10
                     | inr H6 => clear H5
                                 cases H6 with
                                 | inl H5 => cases H5 with | intro y H6 =>
                                             cases (em (y = ↑v)) with
                                             | inl H7 => subst H7
                                                         left
                                                         rewrite [Set.ext_iff]
                                                         simp
                                                         intros x_1 _ _ Hx_1 H7 H8
                                                         rewrite [Set.ext_iff] at H6
                                                         simp at H6
                                                         rewrite [H6] at H8
                                                         tauto
                                             | inr H7 => right
                                                         left
                                                         exists y
                                                         rewrite [Set.ext_iff]
                                                         rewrite [Set.ext_iff] at H6
                                                         intros x_1
                                                         apply Iff.intro
                                                         . intro H8
                                                           simp at H8
                                                           simp at H6
                                                           simp
                                                           rewrite [<- H6]
                                                           tauto
                                                         . simp
                                                           intros H8
                                                           subst H8
                                                           simp at H6
                                                           apply And.intro
                                                           . tauto
                                                           . apply And.intro
                                                             . have H8: x_1 ∈ M.verts := by
                                                                 cases M with | mk verts Adj adj_sub edge_vert symm =>
                                                                 simp
                                                                 apply edge_vert
                                                                 simp at H6
                                                                 simp [Symmetric] at symm
                                                                 apply symm
                                                                 rewrite [H6]
                                                                 rfl
                                                               tauto
                                                             . rewrite [H6]
                                                               rfl
                                 | inr H5 => cases H5 with | intro y H5 =>
                                             cases H5 with | intro z H5 =>
                                             cases H5 with | intro H5 H6 =>
                                             cases (em (y = v)) with
                                             | inl H7 => subst H7
                                                         right
                                                         left
                                                         exists z
                                                         rewrite [Set.ext_iff]
                                                         rewrite [Set.ext_iff] at H6
                                                         simp
                                                         simp at H6
                                                         intros x_1
                                                         apply Iff.intro
                                                         . simp
                                                           intros _ _ Hx_1 H7 H8
                                                           rewrite [H6] at H8
                                                           tauto
                                                         . intro H7
                                                           subst H7
                                                           apply And.intro
                                                           . tauto
                                                           . apply And.intro
                                                             . have H7: M.Adj x x_1 := by
                                                                 rewrite [H6]
                                                                 tauto
                                                               cases M with | mk verts Adj adj_sub edge_vert symm =>
                                                               simp
                                                               simp at H7
                                                               simp [Symmetric] at symm
                                                               have H8 := symm H7
                                                               have H9 := edge_vert H8
                                                               tauto
                                                             . rewrite [H6]
                                                               tauto
                                             | inr H7 => cases (em (z = v)) with
                                                         | inl H7 => subst H7
                                                                     right
                                                                     left
                                                                     exists y
                                                                     rewrite [Set.ext_iff]
                                                                     rewrite [Set.ext_iff] at H6
                                                                     simp
                                                                     simp at H6
                                                                     intros x_1
                                                                     apply Iff.intro
                                                                     . simp
                                                                       intros _ _ Hx_1 H7 H8
                                                                       rewrite [H6] at H8
                                                                       tauto
                                                                     . intros H7
                                                                       subst H7
                                                                       apply And.intro
                                                                       . tauto
                                                                       . apply And.intro
                                                                         . have H7: M.Adj x x_1 := by
                                                                             rewrite [H6]
                                                                             tauto
                                                                           cases M with | mk verts Adj adj_sub edge_vert symm =>
                                                                           simp
                                                                           simp at H7
                                                                           simp [Symmetric] at symm
                                                                           have H8 := symm H7
                                                                           have H9 := edge_vert H8
                                                                           tauto
                                                                         . rewrite [H6]
                                                                           tauto
                                                         | inr h => right
                                                                    right
                                                                    exists y, z
                                                                    apply And.intro
                                                                    . tauto
                                                                    . rewrite [<- H6]
                                                                      rewrite [Set.ext_iff]
                                                                      intros x_1
                                                                      simp
                                                                      apply Iff.intro
                                                                      . tauto
                                                                      . intros H8
                                                                        apply And.intro
                                                                        . tauto
                                                                        . apply And.intro
                                                                          . rewrite [Set.ext_iff] at H6
                                                                            simp at H6
                                                                            apply And.intro
                                                                            . cases M with | mk verts Adj adj_sub edge_vert symm =>
                                                                              simp
                                                                              apply edge_vert
                                                                              apply symm
                                                                              simp at H8
                                                                              exact H8
                                                                            . rewrite [H6] at H8
                                                                              cases H8 with
                                                                              | inl H8 => subst H8
                                                                                          assumption
                                                                              | inr H8 => subst H8
                                                                                          assumption
                                                                          . assumption
                   have H4: Mp.verts.encard = ↑(n + 1) := by
                     sorry
                   cases (H0 v.1 v.2) with
                   | inl H5 => have H6 := aux1_subcase_1 M v.1 v.2 H5
                               cases H6 with | intro W H7 =>
                               exists v.1, v.1, W
                   | inr H5 => cases H5 with
                               | inl H6 => cases H6 with | intro u H6 =>
                                           have H7: u ∈ Mp.verts := by
                                             simp
                                             apply And.intro
                                             . cases M with | mk verts Adj adj_sub edge_vert symm =>
                                               simp [SimpleGraph.Subgraph.neighborSet] at H6
                                               rewrite [Set.ext_iff] at H6
                                               simp at H6
                                               have H7: Adj (↑v) u := by
                                                 rewrite [H6]
                                                 rfl
                                               simp
                                               simp [Symmetric] at symm
                                               apply edge_vert
                                               apply symm
                                               exact H7
                                             . cases M with | mk verts Adj adj_sub edge_vert symm =>
                                               simp [SimpleGraph.Subgraph.neighborSet] at H6
                                               rewrite [Set.ext_iff] at H6
                                               simp at H6
                                               have H7: Adj (↑v) u := by
                                                 rewrite [H6]
                                                 rfl
                                               cases G with | mk Adj symm loopless =>
                                               simp [Irreflexive] at loopless
                                               intros H8
                                               subst H8
                                               simp at adj_sub
                                               exact (loopless _ (adj_sub H7))
                                           set cp := Mp.coe.connectedComponentMk ⟨u, H7⟩
                                           have H8 := ih Mp cp MpH H4
                                           cases H8 with | intro x H8 =>
                                           cases H8 with | intro y H8 =>
                                           cases H8 with | intro W H8 =>
                                           exists x, y, W
                                           apply And.intro
                                           . tauto
                                           . cases H8 with | intro H8 H9 =>
                                             rewrite [H9]
                                             apply SimpleGraph.Subgraph.ext
                                             . simp
                                               rewrite [Set.ext_iff]
                                               intros x_2
                                               simp [Lean.Internal.coeM]
                                               apply Iff.intro
                                               . intro H10
                                                 cases H10 with | intro x_1 H10 =>
                                                 cases H10 with | intro H11 H12 =>
                                                 exists x_2
                                                 cases H12 with | intro H12 H13 =>
                                                 simp [CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe] at H13
                                                 subst H13
                                                 exists H11.1
                                                 simp [CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe]
                                                 simp [SimpleGraph.Reachable]
                                                 simp [SimpleGraph.Reachable] at H12
                                                 cases H12 with | intro W_1 =>
                                                 have H12: u ∈ M.verts := by
                                                   simp at H7
                                                   tauto
                                                 clear ih H0 H1 MpH H4 H8 H9
                                                 have W_2: SimpleGraph.Walk (SimpleGraph.Subgraph.coe M)
                                                           { val := x_2, property := H11.1 }
                                                           { val := u, property := H12} := by
                                                   sorry
                                                 have H13: M.coe.Adj v ⟨u, H12⟩ := by
                                                   rewrite [Set.ext_iff] at H6
                                                   simp at H6
                                                   simp
                                                   rewrite [H6]
                                                   rfl
                                                 have W_2_rev := W_2.reverse
                                                 have W_2_rev_cons := SimpleGraph.Walk.cons H13 W_2_rev
                                                 have W_2_rev_cons_rev := W_2_rev_cons.reverse
                                                 constructor
                                                 exact W_2_rev_cons_rev
                                               . intro H10
                                                 cases H10 with | intro x_1 H10 =>
                                                 cases H10 with | intro H11 H12 =>
                                                 
                                                 sorry
                                             .
                                               sorry
                               | inr H6 => cases H6 with | intro u H6 =>
                                           cases H6 with | intro w H6 =>
                                           cases H6 with | intro H6 H7 =>
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
