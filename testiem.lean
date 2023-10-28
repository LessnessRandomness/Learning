import Mathlib.Init.Function
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card

def aux0 {V} [Fintype V] {G: SimpleGraph V} (M: G.Subgraph) [DecidableRel M.Adj]:
  ∀ (x: V), x ∈ M.verts → M.degree x ≤ 2 := by sorry

def aux1 {V} [Fintype V] {G: SimpleGraph V} (M1 M2: G.Subgraph)
  [DecidablePred fun x => x ∈ M1.support] [DecidablePred fun x => x ∈ M2.support]:
  M1.support.toFinset.card ≤ M2.support.toFinset.card := by sorry
