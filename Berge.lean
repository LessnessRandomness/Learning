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

theorem aux1_subcase_2 {V} [F: Fintype V] {G: SimpleGraph V} (M: G.Subgraph):
  ∀ (x: V) (H: x ∈ M.verts) (H0: ∃ (y: V), M.neighborSet x = {y}),
  ∃ (z: V) (W: G.Walk x z), W.IsTrail ∧
  W.toSubgraph = M.induce (M.coe.connectedComponentMk ⟨x, H⟩).supp := by
    intros x H
    have H0: ∃ (n: Nat), M.verts.encard = ↑n := by
      sorry
    intros H1
    cases H0 with | intro w h =>
    revert M x
    induction w with
    | zero => simp
              intros M x H x_1 H0 H1
              rewrite [Set.ext_iff] at H1
              simp at H1
              exfalso
              exact (H1 _ H)
    | succ n ih => simp at *
                   intros M x H x_1 H0 H1
                   set M' := M.deleteVerts {x}
                   have H2: M = M.induce (M'.verts ∪ {x}) := by
                     apply SimpleGraph.Subgraph.ext
                     . simp
                       simp [insert]
                       simp [Set.insert]
                       rewrite [Set.ext_iff]
                       intros x_2
                       simp
                       apply Iff.intro
                       . intros H2
                         right
                         assumption
                       . intros H2
                         cases H2 with
                         | inl H2 => subst H2
                                     assumption
                         | inr H2 => assumption
                     . apply funext
                       intros x_2
                       apply funext
                       intros x_3
                       simp
                       apply Iff.intro
                       . intros H2
                         apply And.intro
                         . right
                           cases M with | mk verts Adj adj_sub edge_vert symm =>
                           simp at *
                           apply edge_vert
                           exact H2
                         . apply And.intro
                           . right
                             cases M with | mk verts Adj adj_sub edge_vert symm =>
                             simp at *
                             apply edge_vert
                             simp [Symmetric] at symm
                             apply (symm H2)
                           . assumption
                       . tauto
                   cases (em (M'.verts = ∅)) with
                   | inl H3 => rewrite [H3] at H2
                               simp at H2
                               clear ih
                               exists x, SimpleGraph.Walk.nil (u := x)
                               simp
                               apply SimpleGraph.Subgraph.ext
                               . simp
                                 simp [SimpleGraph.Subgraph.induce] at H2
                                 cases M with | mk verts Adj adj_sub edge_vert symm =>
                                 simp at *
                                 cases H2 with | intro left right =>
                                 clear H3
                                 subst left
                                 simp [SimpleGraph.Subgraph.coe]
                                 simp [SimpleGraph.ConnectedComponent.supp]
                                 simp [SimpleGraph.Reachable]
                                 simp [Lean.Internal.coeM]
                                 simp [CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe]
                                 simp [Set.iUnion]
                               . simp [SimpleGraph.singletonSubgraph]
                                 cases M with | mk verts Adj adj_sub edge_vert symm =>
                                 simp
                                 simp [SimpleGraph.Subgraph.induce]
                                 apply funext
                                 intros x_2
                                 apply funext
                                 intros x_3
                                 simp
                                 apply Iff.intro
                                 . tauto
                                 . simp [SimpleGraph.Subgraph.coe]
                                   simp [SimpleGraph.ConnectedComponent.supp]
                                   simp [SimpleGraph.Reachable]
                                   simp [Lean.Internal.coeM]
                                   simp [CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe]
                                   intros x_4 H4 W H5 x_6 H6 W' H7 H8
                                   subst H5
                                   subst H7
                                   simp at H
                                   simp at H1
                                   simp [SimpleGraph.Subgraph.induce] at H2
                                   cases H2 with | intro left right =>
                                   subst left
                                   simp at *
                                   simp at H4
                                   subst H4
                                   simp at H6
                                   subst H6
                                   cases G with | mk Adj' symm' loopless =>
                                   simp [Irreflexive] at loopless
                                   simp at adj_sub
                                   set H9 := adj_sub H8
                                   set H10 := loopless _ H9
                                   assumption
                   | inr H3 => rewrite [Set.ext_iff] at H3
                               have H4: ∃ x, x ∈ M'.verts := by
                                 simp at H3
                                 cases H3 with | intro w h =>
                                 exists w
                               clear H3
                               cases H4 with | intro w h =>
                               have H3 := ih M' w h
                               clear ih
                               cases (em (M'.verts = {w})) with
                               | inl H4 => rewrite [Set.ext_iff] at H4
                                           exists w
                                           have H5: M.Adj x w := by
                                             simp at H4
                                             cases M with | mk verts Adj adj_sub edge_vert symm =>
                                             simp [SimpleGraph.Subgraph.neighborSet] at H0
                                             simp
                                             rewrite [Set.ext_iff] at H0
                                             simp at H0
                                             rewrite [H0]
                                             simp at H2
                                             simp at H4
                                             have H6: x_1 = w := by
                                               rewrite [<- H4]
                                               simp at H
                                               apply And.intro
                                               . apply (@edge_vert _ x)
                                                 simp [Symmetric] at symm
                                                 apply symm
                                                 rewrite [H0]
                                                 rfl
                                               . intro H7
                                                 subst H7
                                                 have H8: Adj x_1 x_1 := by
                                                   rewrite [H0]
                                                   rfl
                                                 cases G with | mk Adj' symm loopless =>
                                                 simp [Irreflexive] at loopless
                                                 simp at adj_sub
                                                 exact (loopless _ (adj_sub H8))
                                             subst H6
                                             rfl
                                           have H6: G.Adj x w := by
                                             cases M with | mk verts Adj adj_sub edge_vert symm =>
                                             apply adj_sub
                                             simp at H5
                                             assumption
                                           exists (SimpleGraph.Walk.cons H6 (SimpleGraph.Walk.nil (u := w)))
                                           apply And.intro
                                           . simp
                                           . simp
                                             simp [SimpleGraph.ConnectedComponent.supp]
                                             simp [SimpleGraph.Reachable]
                                             simp [SimpleGraph.Subgraph.coe]
                                             simp [Lean.Internal.coeM]
                                             simp [CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe]
                                             simp [SimpleGraph.Subgraph.induce]
                                             simp [SimpleGraph.subgraphOfAdj]
                                             rewrite [Set.ext_iff]
                                             simp
                                             apply And.intro
                                             . intros x_2
                                               apply Iff.intro
                                               . intros H7
                                                 cases H7 with
                                                 | inl H7 => subst H7
                                                             exists H
                                                             constructor
                                                             constructor
                                                 | inr H7 => subst H7
                                                             simp at h
                                                             cases h with | intro left right =>
                                                             exists left
                                                             constructor
                                                             sorry
                                               . sorry
                                             . sorry
                               | inr H4 => sorry







theorem aux1_subcase_3 {V} [F: Fintype V] {G: SimpleGraph V} (M: G.Subgraph):
  ∀ (c: M.coe.ConnectedComponent)
  (H: ∀ x, x ∈ c.supp → ∃ x1 x2, x1 ≠ x2 ∧ M.neighborSet x = {x1, x2}),
  ∃ (x: V) (W: G.Walk x x), W.IsCycle ∧ W.toSubgraph = M.induce c.supp := by
    sorry

theorem aux1 {V} [F: Fintype V] [D: DecidableEq V] {G: SimpleGraph V} (M: G.Subgraph):
  (∀ (x: V), x ∈ M.verts → (M.neighborSet x).encard ≤ 2) →
  ∀ (c: M.coe.ConnectedComponent),
  ∃ (x y: V) (W: G.Walk x y), W.IsTrail ∧ W.toSubgraph = M.induce c.supp := by
    intros H
    have H0: (∀ (x: V), x ∈ M.verts →
      M.neighborSet x = ∅ ∨
      (∃ x1, M.neighborSet x = {x1}) ∨
      (∃ x1 x2, x1 ≠ x2 ∧ M.neighborSet x = {x1, x2})) := by
        intros x H0
        exact (encard_aux1 _ (H x H0))
    clear H
    intros c
    cases (em (∃ v, v ∈ c.supp ∧ M.neighborSet v = ∅)) with
    | inl H1 => cases H1 with | intro v H1 =>
                cases H1 with | intro left right =>
                set H1 := aux1_subcase_1 M v.1 v.2 right
                cases H1 with | intro W H1 =>
                exists ↑v, ↑v, W
                cases H1 with | intro left0 right0 =>
                apply And.intro
                . assumption
                . rewrite [right0]
                  have H1: c = SimpleGraph.connectedComponentMk (SimpleGraph.Subgraph.coe M) v := by
                    revert c
                    apply SimpleGraph.ConnectedComponent.ind
                    intros v_1 H1
                    simp
                    simp at H1
                    apply SimpleGraph.Reachable.symm
                    assumption
                  tauto
    | inr H1 => have H2: ∀ v, v ∈ c.supp → M.neighborSet ↑v ≠ ∅ := by
                  intros v H2 H3
                  apply H1
                  exists v
                clear H1
                cases (em (∃ v, v ∈ c.supp ∧ (∃ x, M.neighborSet v = {x}))) with
                | inl H3 => cases H3 with | intro w H3 =>
                            cases H3 with | intro left right =>
                            cases right with | intro x H3 =>
                            have H4: ∃ y, SimpleGraph.Subgraph.neighborSet M ↑w = {y} := by
                              exists x
                            cases (aux1_subcase_2 M w.1 w.2 H4) with | intro w0 H5 =>
                            cases H5 with | intro W H5 =>
                            cases H5 with | intro left0 right =>
                            exists ↑w, w0, W
                            apply And.intro
                            . assumption
                            . rewrite [right]
                              have H5: c = SimpleGraph.connectedComponentMk (SimpleGraph.Subgraph.coe M) w := by
                                revert c
                                apply SimpleGraph.ConnectedComponent.ind
                                intros v_1 H1
                                simp
                                intros H2
                                apply SimpleGraph.Reachable.symm
                                assumption
                              tauto
                | inr H3 => have H4: ∀ (v: ↑M.verts), v ∈ c.supp → ∃ x y, x ≠ y ∧
                                                      M.neighborSet v = {x, y} := by
                              intros v H4
                              cases v with | mk v0 H5 =>
                              set H6 := H0 v0 H5
                              cases H6 with
                              | inl H7 => exfalso
                                          set H8 := H2 ⟨v0, H5⟩ H4 H7
                                          assumption
                              | inr H7 => clear H6
                                          cases H7 with
                                          | inl H7 => exfalso
                                                      apply H3
                                                      exists ⟨v0, H5⟩
                                          | inr H7 => assumption
                            set H5 := aux1_subcase_3 M c H4
                            cases H5 with | intro w H6 =>
                            cases H6 with | intro W H7 =>
                            exists w, w, W
                            cases H7 with | intro left right =>
                            cases left with | mk toIsCircuit support_nodup =>
                            cases toIsCircuit with | mk toIsTrail ne_nil =>
                            apply And.intro
                            . assumption
                            . assumption


/-
    apply SimpleGraph.ConnectedComponent.ind
    intros v
    set H1 := H0 v.1 v.2
    cases H1 with
    | inl H2 => clear H1
                set H3 := aux1_subcase_1 M v.1 v.2 H2
                cases H3 with | intro W H4 =>
                exists v.1, v.1, W
    | inr H2 => cases H2 with
                | inl H2 => cases H2 with | intro x H2 =>
                            set H3 := aux1_subcase_2 M v.1 v.2
                            have H4: ∃ y, SimpleGraph.Subgraph.neighborSet M ↑v = {y} := by
                              exists x
                            set H5 := H3 H4
                            cases H5 with | intro w H6 =>
                            cases H6 with | intro W H7 =>
                            exists ↑v, w, W
                | inr H2 => cases H2 with | intro w1 H2 =>
                            cases H2 with | intro w2 H2 =>
                            cases H2 with | intro left right =>
                            set H2 := aux1_subcase_3 M
                            sorry
-/


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
