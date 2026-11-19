import NativeTransitiveRestFrame
import SRNativeFrameOccupation
import TravelTimePolarization

/-! Earliest ray arrivals and actual rest interchanges on one spatial source. -/
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
noncomputable section
set_option autoImplicit false
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open scoped Matrix

/-- The ray family is fixed. A comparison subgroup determines which event moves
are available as proper rest operations. -/
inductive RestProtocolQuery where
  | arrival (z : SREvent)
  | interchange (z w : SREvent)

def restProtocolAnswers (H : Subgroup SRMatrixFrame) : RestProtocolQuery → Prop
  | .arrival z => FiniteReach srOriginalFutureRayIncrements z
  | .interchange z w => ∃ A ∈ H, srIsOriginalProperRestRotation A ∧ srMatrixFrameEvent A z = w

private def firstSpatial : SRSpace := EuclideanSpace.single 0 1

private theorem firstSpatial_norm : ‖firstSpatial‖ = 1 := by
  simp [firstSpatial]

private theorem halfTurn_interchanges :
    srMatrixFrameEvent srSpatialHalfTurnUnit (1,firstSpatial) = (1,-firstSpatial) := by
  apply srEventCoordinates.injective
  rw [sr_event_frame_coordinate_square]
  have hz : (2 : Fin 3) ≠ 0 := by decide
  ext j
  fin_cases j <;>
    norm_num [srSpatialHalfTurnUnit, srSpatialHalfTurn, srEventCoordinates, firstSpatial,
      EuclideanSpace.single_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hz]

private theorem firstSpatial_distinct : firstSpatial ≠ -firstSpatial := by
  intro h
  have contra := congrArg (fun u : SRSpace => u (0 : Fin 3)) h
  norm_num [firstSpatial, EuclideanSpace.single_apply] at contra

private theorem identity_fixes_event (z : SREvent) : srMatrixFrameEvent 1 z = z := by
  apply srEventCoordinates.injective
  rw [sr_event_frame_coordinate_square]
  simp

/-- All finite ray arrivals still agree after retaining the identity comparison
alone. An original proper rest half-turn between opposite one-tick endpoints is
then unavailable. Both endpoints are on the actual earliest-arrival frontier. -/
theorem same_ray_arrivals_can_lose_original_rest_interchange {μ : ℝ}
    (source : SRCalibratedFrameSource μ) :
    (∀ z : SREvent, restProtocolAnswers source.comparisons (.arrival z) ↔
      restProtocolAnswers ⊥ (.arrival z)) ∧
    ∃ x y : SRSpace, x ≠ y ∧
      IsLeast {t : ℝ | restProtocolAnswers source.comparisons (.arrival (t,x))} 1 ∧
      IsLeast {t : ℝ | restProtocolAnswers source.comparisons (.arrival (t,y))} 1 ∧
      restProtocolAnswers source.comparisons (.interchange (1,x) (1,y)) ∧
      ¬ restProtocolAnswers ⊥ (.interchange (1,x) (1,y)) := by
  refine ⟨fun _ => Iff.rfl, firstSpatial, -firstSpatial, firstSpatial_distinct, ?_, ?_, ?_, ?_⟩
  · simpa only [restProtocolAnswers, firstSpatial_norm] using
      sr_original_ray_least_arrival firstSpatial
  · simpa only [restProtocolAnswers, norm_neg, firstSpatial_norm] using
      sr_original_ray_least_arrival (-firstSpatial)
  · have role := sr_spatial_half_turn_is_original_proper_rest_rotation
    obtain ⟨Q,hQ,hR⟩ := (sr_original_rest_role_iff_spatial_so3 srSpatialHalfTurnUnit).mp role
    refine ⟨srSpatialHalfTurnUnit, ?_, role, halfTurn_interchanges⟩
    rw [← hR]
    exact source.originalRestFamily Q hQ
  · rintro ⟨A, hA, _, moved⟩
    have id : A = 1 := Subgroup.mem_bot.mp hA
    subst A
    rw [identity_fixes_event] at moved
    exact firstSpatial_distinct (congrArg Prod.snd moved)

/-- The original occupied source itself supplies a separated rest query, with
the same complete arrival family as the restricted presentation. -/
theorem occupied_rest_answers_differ_despite_all_ray_arrivals :
    let source := srNativeOccupiedFrameSource (1 : ℝ) (by norm_num)
    (∀ z, restProtocolAnswers source.comparisons (.arrival z) ↔
      restProtocolAnswers ⊥ (.arrival z)) ∧
      ∃ z w, restProtocolAnswers source.comparisons (.interchange z w) ∧
        ¬ restProtocolAnswers ⊥ (.interchange z w) := by
  dsimp only
  obtain ⟨arrivals, x, y, _, _, _, present, absent⟩ :=
    same_ray_arrivals_can_lose_original_rest_interchange
      (srNativeOccupiedFrameSource (1 : ℝ) (by norm_num))
  exact ⟨arrivals, (1,x), (1,y), present, absent⟩

end
end AASCKleinGordon.CanonicalLicensing.SRIntegration
