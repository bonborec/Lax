import Lax379983.FeedbackNumberComparison

namespace Lax379983Proofs

open Lax379983.FeedbackVertexNumber Lax379983.FeedbackEdgeNumber

/--
---
conclusion: Lax379983.FeedbackNumberComparison.feedbackVertexNumber_le_feedbackEdgeNumber
---
Choose a minimum feedback edge set $F$ and one endpoint of each edge in $F$.
The set $S$ of chosen endpoints has cardinality at most $|F|$. Every edge of
the induced graph $G[V\setminus S]$ remains in $G-F$, so this induced graph
is acyclic. Thus $S$ is a feedback vertex set and
$\operatorname{FVN}(G)\leq |S|\leq |F|=\operatorname{FEN}(G)$.
-/
theorem feedbackVertexNumber_le_feedbackEdgeNumber {V : Type*} [Finite V]
    (G : SimpleGraph V) : feedbackVertexNumber G ≤ feedbackEdgeNumber G := by
  classical
  have hnonempty : {n : ℕ | ∃ F : Set (Sym2 V),
      F ⊆ G.edgeSet ∧ F.ncard = n ∧ (G.deleteEdges F).IsAcyclic}.Nonempty := by
    exact ⟨G.edgeSet.ncard, G.edgeSet, Set.Subset.rfl, rfl, by simp⟩
  obtain ⟨F, _hF, hcard, hacyclic⟩ : ∃ F : Set (Sym2 V),
      F ⊆ G.edgeSet ∧ F.ncard = feedbackEdgeNumber G ∧ (G.deleteEdges F).IsAcyclic :=
    csInf_mem hnonempty
  let S : Set V := (fun e : Sym2 V => e.out.1) '' F
  let inclusion : (G.induce Sᶜ) →g G.deleteEdges F :=
    { toFun := Subtype.val
      map_rel' := by
        intro v w hvw
        apply SimpleGraph.deleteEdges_adj.mpr
        refine ⟨hvw, ?_⟩
        intro he
        have hselected : (s(v.val, w.val) : Sym2 V).out.1 ∈ S :=
          Set.mem_image_of_mem _ he
        rcases Sym2.mem_iff.mp (Sym2.out_fst_mem s(v.val, w.val)) with h | h
        · exact v.property (h ▸ hselected)
        · exact w.property (h ▸ hselected) }
  have hS : (G.induce Sᶜ).IsAcyclic :=
    hacyclic.comap inclusion Subtype.val_injective
  calc
    feedbackVertexNumber G ≤ S.ncard := csInf_le' ⟨S, rfl, hS⟩
    _ ≤ F.ncard := Set.ncard_image_le
    _ = feedbackEdgeNumber G := hcard

end Lax379983Proofs
