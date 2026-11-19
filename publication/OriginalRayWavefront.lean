import WavefrontWitness
import SROccupiedRayReach

/-! The wavefront experiment in the unification project's original unit-ray
carrier. Its finite-ledger relation and its completion yield the same readings. -/
namespace AASCWavefront

open AASCMetricConstruction
set_option autoImplicit false

theorem six_events_on_original_ray_ledgers {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (different : x ≠ y) (not_opposite : x ≠ -y) :
    ∃ s : Fin 3 → E, (∀ i, ‖s i‖ = 1) ∧ ∃ t : ℝ, 0 < t ∧ t < 2 ∧
      ∀ i j, (FiniteReach srOriginalFutureRayIncrements (t, -s j-s i) ↔ i ≠ j) ∧
        ((t, -s j-s i) ∈ completedReach srOriginalFutureRayIncrements ↔ i ≠ j) := by
  letI := nontrivial_of_ne x y different
  obtain ⟨s, unit, t, positive, bound, pattern⟩ :=
    six_events_of_two_directions x y hx hy different not_opposite
  refine ⟨s, unit, t, positive, bound, fun i j => ⟨?_, ?_⟩⟩
  · exact (sr_original_ray_finite_reach_exact_full_cone _).trans (pattern i j)
  · rw [sr_original_ray_completed_reach_exact_full_cone]
    exact pattern i j

end AASCWavefront
