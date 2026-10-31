import SchauderFixedPointTheorem.Sperner
import Architect
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Set.Operations

namespace SchauderFixedPointTheorem

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Schauder fixed point theorem (statement)**: a continuous self-map of a nonempty compact
convex subset of a Banach space has a fixed point. The proof combines the ordered lattice
Sperner theorem with the compact-convex reduction. -/
@[blueprint "SchauderFixedPointTheorem.MainTheorem"]
theorem MainTheorem {s : Set E} (hs_nonempty : s.Nonempty) (hs_compact : IsCompact s)
    (hs_convex : Convex ℝ s) {f : E → E} (hf_cont : ContinuousOn f s)
    (hf_maps : Set.MapsTo f s s) :
    ∃ x ∈ s, f x = x := by
  exact schauder_of_lattice_sperner lattice_sperner hs_nonempty hs_compact hs_convex hf_cont hf_maps

end SchauderFixedPointTheorem
