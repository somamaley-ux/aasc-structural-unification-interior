import SRNativeWholeSourceComparisons
import SRNativeClockLorentzAttachment
import SRConeConstructedMetricActionSource

/-! Join the same weak-order/proper-rotation source to the full form, native
clock-rate receipt and prior actual scalar action/source theorem. No strict
completed-clock or target metric field is input to the last theorem. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

theorem sr_native_oriented_order_constructor_matches_full_original_ray_form
    (dimension:2≤Module.finrank ℝ E) :
    srSourceLorentzForm (srRayClock (E:=E)) (srRayRestVector (E:=E))
      (sr_ray_rest_clock_one (E:=E))
      (srCompletedOrderToConeSource (srRayClock (E:=E)) (srRayRestVector (E:=E))
        (srNativeOrientedCompletedOrderSource (E:=E) dimension))=
    srSourceLorentzForm (srRayClock (E:=E)) (srRayRestVector (E:=E))
      (sr_ray_rest_clock_one (E:=E)) (srOccupiedIsotropicRaySource (E:=E)) := by
  let s:=srCompletedOrderToConeSource (srRayClock (E:=E)) (srRayRestVector (E:=E))
    (srNativeOrientedCompletedOrderSource (E:=E) dimension)
  let t:=srOccupiedIsotropicRaySource (E:=E)
  have hg:srSourceSpatialForm (srRayClock (E:=E)) (srRayRestVector (E:=E)) (sr_ray_rest_clock_one (E:=E)) s=
      srSourceSpatialForm (srRayClock (E:=E)) (srRayRestVector (E:=E)) (sr_ray_rest_clock_one (E:=E)) t:=by
    apply sr_positive_quadratic_form_unique_from_full_unit_ball _ _
      (sr_source_spatial_positive (srRayClock (E:=E)) (srRayRestVector (E:=E)) (sr_ray_rest_clock_one (E:=E)) s)
      (sr_source_spatial_positive (srRayClock (E:=E)) (srRayRestVector (E:=E)) (sr_ray_rest_clock_one (E:=E)) t)
    intro x
    exact (sr_source_spatial_recovers_full_clock_body (srRayClock (E:=E)) (srRayRestVector (E:=E))
      (sr_ray_rest_clock_one (E:=E)) s x).symm.trans
      (sr_source_spatial_recovers_full_clock_body (srRayClock (E:=E)) (srRayRestVector (E:=E)) (sr_ray_rest_clock_one (E:=E)) t x)
  exact congrArg (srConstructedLorentzQuadratic (srRayClock (E:=E)) (srRayRestVector (E:=E)) (sr_ray_rest_clock_one (E:=E))) hg

theorem sr_native_same_oriented_order_source_form_matches_actual_clock_rate
    (dimension:2≤Module.finrank ℝ E) (μ0:ℝ) (z:SRNativeClockState E)
    (positive:0<srNativeClockMass μ0 z) :
    srSourceLorentzForm (srRayClock (E:=E)) (srRayRestVector (E:=E))
      (sr_ray_rest_clock_one (E:=E))
      (srCompletedOrderToConeSource (srRayClock (E:=E)) (srRayRestVector (E:=E))
        (srNativeOrientedCompletedOrderSource (E:=E) dimension))
      (1,srNativeClockVelocity μ0 z)=(srNativeClockRate μ0 z)^2 := by
  rw [sr_native_oriented_order_constructor_matches_full_original_ray_form dimension]
  exact sr_native_clock_rate_matches_full_constructed_lorentz_form μ0 z positive

open AASCSemanticExhaustion TopologicalSpace

theorem sr_original_weak_order_constructs_actual_scalar_action_and_unique_source
    (τ:CoordinatePoint →L[ℝ] ℝ) [Nontrivial (SRClockSpatialSpace τ)]
    (e:CoordinatePoint) (clockOne:τ e=1) {H:Type} [Group H]
    {Ω:Opens CoordinatePoint} (s:SRCompletedOrderSource (H:=H) τ e)
    (χ:CoordinatePoint → ℝ) (hχ:ContDiff ℝ 2 χ) (μ:ℝ) :
    (∀ p,(srSourceConstructedMetric τ e clockOne (srCompletedOrderToConeSource τ e s) p).det≠0) ∧
    ∃! T:SymmetricSourceComponents Ω,∀ h,
      (1/2:ℝ)*metricSourcePairing T h=nativeActionDirectional
        (nativeScalarClockRelativeAction
          (srSourceConstructedMetric τ e clockOne (srCompletedOrderToConeSource τ e s)) χ μ) h :=
  sr_full_original_cone_constructs_actual_scalar_action_and_unique_source τ e clockOne
    (srCompletedOrderToConeSource τ e s) χ hχ μ

#print axioms sr_native_oriented_order_constructor_matches_full_original_ray_form
#print axioms sr_native_same_oriented_order_source_form_matches_actual_clock_rate
#print axioms sr_original_weak_order_constructs_actual_scalar_action_and_unique_source
end
end AASCMetricConstruction
