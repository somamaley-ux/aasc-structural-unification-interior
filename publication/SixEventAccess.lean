import ExactPairMeetings
import OriginalRayWavefront

/-! A test of causal access on the manuscript's original clock-and-ray preparation. -/
namespace AASCWavefront

open AASCMetricConstruction
set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

/-- In the original preparation, a finite ledger reaches the receiving site exactly
when the source-to-receiver delay fits between their clock readings. -/
theorem finite_ray_arrival_iff (s t : ℝ) (x y : E) :
    FiniteReach srOriginalFutureRayIncrements (t - s, y - x) ↔
      s + dist x y ≤ t := by
  rw [sr_original_ray_finite_reach_exact_full_cone]
  change ‖y - x‖ ≤ t - s ↔ _
  rw [← dist_eq_norm, dist_comm y x]
  constructor <;> intro h <;> linarith

/-- Exact four-site criterion for six events linked by finite original ledgers,
with freely available sites and real clock readings. -/
theorem original_finite_ledgers_iff_not_four_point :
    (∃ x y : Fin 3 → E, ∃ s t : Fin 3 → ℝ, ∀ i j,
      (FiniteReach srOriginalFutureRayIncrements (t j - s i, y j - x i) ↔ i ≠ j)) ↔
    ¬ AASCPairMeetings.FourPoint E := by
  simpa only [finite_ray_arrival_iff, AASCPairMeetings.SixEventTest] using
    (AASCPairMeetings.six_events_iff_not_four_point (X := E))

end AASCWavefront
