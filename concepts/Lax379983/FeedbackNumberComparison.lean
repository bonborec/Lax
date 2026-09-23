import Lax379983.FeedbackVertexNumber
import Lax379983.FeedbackEdgeNumber

/-!
---
title: Feedback vertex number is at most feedback edge number
type: theorem
---
For every finite undirected simple graph $G$,
$$
\operatorname{FVN}(G)\leq\operatorname{FEN}(G).
$$
No connectedness or nonemptiness assumption is required.
-/

namespace Lax379983.FeedbackNumberComparison

open Lax379983.FeedbackVertexNumber Lax379983.FeedbackEdgeNumber

/-- Every finite simple graph has feedback vertex number at most its feedback edge number. -/
axiom feedbackVertexNumber_le_feedbackEdgeNumber {V : Type*} [Finite V]
    (G : SimpleGraph V) : feedbackVertexNumber G ≤ feedbackEdgeNumber G

end Lax379983.FeedbackNumberComparison
