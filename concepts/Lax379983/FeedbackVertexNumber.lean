import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card

/-!
---
title: Feedback vertex number
type: definition
---
Let $G=(V,E)$ be a finite undirected simple graph. A feedback vertex set is a
set $S\subseteq V$ for which the induced graph $G[V\setminus S]$ is acyclic.
The feedback vertex number is
$$
\operatorname{FVN}(G)=\min\{\lvert S\rvert : S\subseteq V,\;
G[V\setminus S]\text{ is acyclic}\}.
$$
The minimum exists because deleting all vertices leaves an acyclic graph.
-/

namespace Lax379983.FeedbackVertexNumber

/-- The minimum number of vertices whose deletion makes the graph acyclic. -/
noncomputable def feedbackVertexNumber {V : Type*} [Finite V] (G : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ S : Set V, S.ncard = n ∧ (G.induce Sᶜ).IsAcyclic}

end Lax379983.FeedbackVertexNumber
