import SROccupiedRayReach
import Mathlib.Topology.Homeomorph.Defs

namespace AASCMetricConstruction.SRIntegration
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set
open scoped Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sr_native_future_cone_interior :
    interior (srRayFutureCone (E:=E)) = {z : ℝ × E | ‖z.2‖ < z.1} := by
  apply Set.Subset.antisymm
  · intro z hz
    have inCone : z ∈ (srRayFutureCone (E:=E)) := interior_subset hz
    have nonstrict : ‖z.2‖ ≤ z.1 := inCone
    by_contra strict
    have equal : ‖z.2‖ = z.1 := le_antisymm nonstrict (le_of_not_gt strict)
    obtain ⟨ε,positive,ball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
    let w : ℝ × E := (z.1-ε/2,z.2)
    have inside : w ∈ Metric.ball z ε := by
      change dist w z < ε
      rw [Prod.dist_eq]
      simp only [w,dist_self,Real.dist_eq]
      have habs : |z.1-ε/2-z.1| = ε/2 := by
        rw [show z.1-ε/2-z.1 = -(ε/2) by ring,abs_neg,abs_of_pos (by linarith)]
      rw [habs,max_eq_left (by linarith)]
      linarith
    have contradiction : ‖z.2‖ ≤ z.1-ε/2 := ball inside
    linarith
  · exact interior_maximal
      (show {z : ℝ × E | ‖z.2‖ < z.1} ⊆ srRayFutureCone from
        fun z h => (show ‖z.2‖ < z.1 from h).le)
      (isOpen_lt continuous_snd.norm continuous_fst)

theorem sr_native_future_cone_frontier :
    frontier (srRayFutureCone (E:=E)) = {z : ℝ × E | ‖z.2‖ = z.1} := by
  have closed : IsClosed (srRayFutureCone (E:=E)) := isClosed_le continuous_snd.norm continuous_fst
  rw [frontier, closed.closure_eq,
    sr_native_future_cone_interior]
  ext z
  change (‖z.2‖ ≤ z.1 ∧ ¬ ‖z.2‖ < z.1) ↔ ‖z.2‖ = z.1
  exact ⟨fun h => le_antisymm h.1 (le_of_not_gt h.2),fun h => ⟨h.le,by linarith⟩⟩

theorem sr_exact_original_cone_frame_preserves_boundary
    (F : (ℝ × E) ≃ₜ (ℝ × E)) (exactCone : F '' srRayFutureCone = srRayFutureCone)
    (z : ℝ × E) (boundary : ‖z.2‖ = z.1) : ‖(F z).2‖ = (F z).1 := by
  have original : z ∈ frontier (srRayFutureCone (E:=E)) := by
    rw [sr_native_future_cone_frontier]
    exact boundary
  have image : F z ∈ F '' frontier (srRayFutureCone (E:=E)) := ⟨z,original,rfl⟩
  rw [F.image_frontier,exactCone,sr_native_future_cone_frontier] at image
  exact image

theorem sr_exact_original_cone_frame_preserves_strict_clock_body
    (F : (ℝ × E) ≃ₜ (ℝ × E)) (exactCone : F '' srRayFutureCone = srRayFutureCone)
    (z : ℝ × E) (inside : ‖z.2‖ < z.1) : ‖(F z).2‖ < (F z).1 := by
  have original : z ∈ interior (srRayFutureCone (E:=E)) := by
    rw [sr_native_future_cone_interior]
    exact inside
  have image : F z ∈ F '' interior (srRayFutureCone (E:=E)) := ⟨z,original,rfl⟩
  rw [F.image_interior,exactCone,sr_native_future_cone_interior] at image
  exact image

#print axioms sr_exact_original_cone_frame_preserves_boundary
#print axioms sr_exact_original_cone_frame_preserves_strict_clock_body
end
end AASCMetricConstruction.SRIntegration
