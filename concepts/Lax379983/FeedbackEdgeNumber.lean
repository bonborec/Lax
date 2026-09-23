import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card

/-!
---
title: Feedback edge number
type: definition
---
Let $G=(V,E)$ be a finite undirected simple graph. A feedback edge set is a
set $F\subseteq E$ for which the graph $G-F$, obtained by deleting the edges
in $F$ and retaining all vertices, is acyclic. The feedback edge number is
$$
\operatorname{FEN}(G)=\min\{\lvert F\rvert : F\subseteq E,\;
G-F\text{ is acyclic}\}.
$$
The minimum exists because deleting all edges leaves an acyclic graph.
-/

namespace Lax379983.FeedbackEdgeNumber

/-- The minimum number of edges whose deletion makes the graph acyclic. -/
noncomputable def feedbackEdgeNumber {V : Type*} [Finite V] (G : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ F : Set (Sym2 V),
    F ⊆ G.edgeSet ∧ F.ncard = n ∧ (G.deleteEdges F).IsAcyclic}

end Lax379983.FeedbackEdgeNumber
