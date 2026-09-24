import Lax379983.TreewidthBound

namespace Lax379983Proofs

open Lax228581.Treewidth Lax379983.FeedbackVertexNumber

/-- A finite forest has a tree decomposition with bags of size at most two. -/
private theorem forest_decomposition {V : Type} [Fintype V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) : ∃ D : TreeDecomposition G, ∀ i, (D.bag i).card ≤ 2 := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h =>
    let D : TreeDecomposition G :=
      { Node := Unit
        tree := ⊥
        isTree := ⟨SimpleGraph.connected_bot_iff.mpr ⟨inferInstance, inferInstance⟩,
          SimpleGraph.isAcyclic_bot⟩
        bag := fun _ => ∅
        vertex_mem_bag := fun v => isEmptyElim v
        edge_mem_bag := fun {v} => isEmptyElim v
        bag_indices_connected := fun v => isEmptyElim v }
    exact ⟨D, by intro i; simp [D]⟩
  | inr h =>
    obtain ⟨T, hGT, _, hT⟩ :=
      (SimpleGraph.connected_top (V := V)).exists_isTree_le_of_le_of_isAcyclic
        (H := G) le_top hG
    let r : V := Classical.choice h
    choose p hp using fun v => hT.connected.exists_isPath r v
    let bag : V → Finset V := fun v => {v, (p v).penultimate}
    have hparent (v : V) (hne : (p v).penultimate ≠ v) :
        T.Adj (p v).penultimate v := by
      apply SimpleGraph.Walk.adj_penultimate
      intro hn
      apply hne
      have hnil : ∀ {a b : V} {q : T.Walk a b}, q.Nil → q.penultimate = b := by
        intro a b q hq
        cases hq
        rfl
      exact hnil hn
    let D : TreeDecomposition G :=
      { Node := V
        tree := T
        isTree := hT
        bag := bag
        vertex_mem_bag := fun v => ⟨v, by simp [bag]⟩
        edge_mem_bag := by
          intro u v huv
          have ht := hGT huv
          by_cases hu : u ∈ (p v).support
          · have he := hT.isAcyclic.eq_penultimate_of_adj_end (hp v) ht.symm hu
            exact ⟨v, by simp [bag, he], by simp [bag]⟩
          · have hv := hT.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
              (hp u) (hp v) ht hu
            have he := hT.isAcyclic.eq_penultimate_of_adj_end (hp u) ht hv
            exact ⟨u, by simp [bag], by simp [bag, he]⟩
        bag_indices_connected := by
          intro v
          apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
          refine ⟨⟨v, by simp [bag]⟩, ?_⟩
          intro i
          by_cases hi : v = i.val
          · have he : (⟨v, by simp [bag]⟩ : {i // v ∈ bag i}) = i :=
              Subtype.ext hi
            rw [he]
          · have he : v = (p i.val).penultimate := by
              simpa [bag, hi] using i.property
            apply SimpleGraph.Adj.reachable
            change T.Adj v i.val
            simpa only [← he] using hparent i.val (by simpa only [← he] using hi) }
    refine ⟨D, fun i => ?_⟩
    exact (Finset.card_insert_le _ _).trans (by simp)

/-- Restore the deleted vertices by placing them in every bag. -/
private noncomputable def addFeedbackSet {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Set V) (D : TreeDecomposition (G.induce Sᶜ)) :
    TreeDecomposition G := by
  classical
  let bag := fun i => S.toFinset ∪ (D.bag i).image Subtype.val
  have hmem (v : V) (i : D.Node) :
      v ∈ bag i ↔ v ∈ S ∨ ∃ hv : v ∈ Sᶜ, (⟨v, hv⟩ : ↑(Sᶜ)) ∈ D.bag i := by
    simp only [bag, Finset.mem_union, Set.mem_toFinset, Finset.mem_image]
    constructor
    · rintro (h | ⟨w, hw, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨w.property, hw⟩
    · rintro (h | ⟨hv, hi⟩)
      · exact Or.inl h
      · exact Or.inr ⟨⟨v, hv⟩, hi, rfl⟩
  let root : D.Node := Classical.choice D.isTree.connected.nonempty
  refine
    { Node := D.Node
      nodeFintype := D.nodeFintype
      tree := D.tree
      isTree := D.isTree
      bag := bag
      vertex_mem_bag := ?_
      edge_mem_bag := ?_
      bag_indices_connected := ?_ }
  · intro v
    by_cases hv : v ∈ S
    · exact ⟨root, (hmem v root).mpr (Or.inl hv)⟩
    · obtain ⟨i, hi⟩ := D.vertex_mem_bag ⟨v, hv⟩
      exact ⟨i, (hmem v i).mpr (Or.inr ⟨hv, hi⟩)⟩
  · intro u v huv
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
    · exact ⟨root, (hmem u root).mpr (Or.inl hu), (hmem v root).mpr (Or.inl hv)⟩
    · obtain ⟨i, hi⟩ := D.vertex_mem_bag ⟨v, hv⟩
      exact ⟨i, (hmem u i).mpr (Or.inl hu), (hmem v i).mpr (Or.inr ⟨hv, hi⟩)⟩
    · obtain ⟨i, hi⟩ := D.vertex_mem_bag ⟨u, hu⟩
      exact ⟨i, (hmem u i).mpr (Or.inr ⟨hu, hi⟩), (hmem v i).mpr (Or.inl hv)⟩
    · obtain ⟨i, hui, hvi⟩ := D.edge_mem_bag (u := ⟨u, hu⟩) (v := ⟨v, hv⟩) huv
      exact ⟨i, (hmem u i).mpr (Or.inr ⟨hu, hui⟩),
        (hmem v i).mpr (Or.inr ⟨hv, hvi⟩)⟩
  · intro v
    by_cases hv : v ∈ S
    · have hset : {i | v ∈ bag i} = (Set.univ : Set D.Node) := by
        ext i
        simp [hmem, hv]
      rw [hset]
      exact (SimpleGraph.induceUnivIso D.tree).connected_iff.mpr D.isTree.connected
    · have hset : {i | v ∈ bag i} = {i | (⟨v, hv⟩ : ↑(Sᶜ)) ∈ D.bag i} := by
        ext i
        simp [hmem, hv]
      rw [hset]
      exact D.bag_indices_connected ⟨v, hv⟩

/--
---
conclusion: Lax379983.TreewidthBound.treewidth_le_feedbackVertexNumber_add_one
---
Choose a minimum feedback vertex set $S$. The remaining forest has a tree
decomposition with at most two vertices in each bag: for a nonempty forest,
extend it to a tree, root it, and use each vertex together with its parent as
a bag, with a singleton bag at the root. For the empty forest, use one empty bag.
Adding $S$ to every bag covers all original edges and preserves connectedness
of the bags containing each vertex. Each new bag has at most $|S|+2$ vertices,
so its width is at most $|S|+1$.
-/
theorem treewidth_le_feedbackVertexNumber_add_one {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : treewidth G ≤ feedbackVertexNumber G + 1 := by
  classical
  have hnonempty : {n : ℕ | ∃ S : Set V,
      S.ncard = n ∧ (G.induce Sᶜ).IsAcyclic}.Nonempty := by
    refine ⟨(Set.univ : Set V).ncard, Set.univ, rfl, ?_⟩
    change (G.induce (Set.univ : Set V)ᶜ).IsAcyclic
    rw [Set.compl_univ]
    exact SimpleGraph.IsAcyclic.of_subsingleton
  obtain ⟨S, hcard, hS⟩ : ∃ S : Set V,
      S.ncard = feedbackVertexNumber G ∧ (G.induce Sᶜ).IsAcyclic :=
    csInf_mem hnonempty
  obtain ⟨D, hD⟩ := forest_decomposition (G.induce Sᶜ) hS
  apply csInf_le'
  refine ⟨addFeedbackSet G S D, fun i => ?_⟩
  change (S.toFinset ∪ (D.bag i).image Subtype.val).card ≤ feedbackVertexNumber G + 1 + 1
  calc
    _ ≤ S.toFinset.card + ((D.bag i).image Subtype.val).card := Finset.card_union_le _ _
    _ ≤ S.toFinset.card + (D.bag i).card := Nat.add_le_add_left Finset.card_image_le _
    _ ≤ S.toFinset.card + 2 := Nat.add_le_add_left (hD i) _
    _ = feedbackVertexNumber G + 1 + 1 := by
      rw [← Set.ncard_eq_toFinset_card', hcard]

end Lax379983Proofs
