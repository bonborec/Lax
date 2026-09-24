import Lax228581.Treewidth
import Lax379983.FeedbackVertexNumber

/-!
---
title: Treewidth is at most feedback vertex number plus one
type: theorem
---
For every finite undirected simple graph $G$,
$$
\operatorname{tw}(G)\leq\operatorname{FVN}(G)+1.
$$
Here treewidth is the least $w$ for which a tree decomposition exists with
every bag of size at most $w+1$. The bound also holds for empty and
disconnected graphs.
-/

namespace Lax379983.TreewidthBound

open Lax228581.Treewidth Lax379983.FeedbackVertexNumber

/-- Every finite simple graph has treewidth at most its feedback vertex number plus one. -/
axiom treewidth_le_feedbackVertexNumber_add_one {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : treewidth G ≤ feedbackVertexNumber G + 1

end Lax379983.TreewidthBound
