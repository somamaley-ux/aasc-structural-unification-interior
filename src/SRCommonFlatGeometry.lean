import SRJointOriginalSource
import SRFrameQuadraticRigidity

/-! Exact carrier and sign identification on the common flat branch H=0.
The independently admitted nonzero EH operands remain available in the joint
source; no equality of those perturbed metrics with flat SR is asserted. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCSemanticExhaustion AASCMetricConstruction
open scoped Matrix BigOperators

def srEventCoordinates : SREvent ≃ₗ[ℝ] CoordinatePoint where
  toFun := fun z => ![z.1,z.2 0,z.2 1,z.2 2]
  invFun := fun p => (p 0,(EuclideanSpace.equiv (Fin 3) ℝ).symm ![p 1,p 2,p 3])
  left_inv := by
    intro z
    apply Prod.ext
    · rfl
    · apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
      ext i
      fin_cases i <;> rfl
  right_inv := by intro p;ext i;fin_cases i <;> rfl
  map_add' := by intro z w;ext i;fin_cases i <;> rfl
  map_smul' := by intro c z;ext i;fin_cases i <;> rfl

def srEventCoordinateEquiv : SREvent ≃L[ℝ] CoordinatePoint :=
  srEventCoordinates.toContinuousLinearEquiv

def srOriginalOrderQuadratic : QuadraticForm ℝ SREvent :=
  srSourceLorentzForm (srRayClock (E:=SRSpace)) (srRayRestVector (E:=SRSpace))
    (sr_ray_rest_clock_one (E:=SRSpace))
    (srCompletedOrderToConeSource (srRayClock (E:=SRSpace)) (srRayRestVector (E:=SRSpace))
      (srNativeOrientedCompletedOrderSource (E:=SRSpace) (by simp)))

theorem sr_original_order_quadratic_computed (z : SREvent) :
    srOriginalOrderQuadratic z = z.1^2 - ‖z.2‖^2 := by
  rw [srOriginalOrderQuadratic,sr_native_oriented_order_constructor_matches_full_original_ray_form,
    sr_full_ray_source_constructor_computes_lorentz_form_everywhere]

theorem sr_source_derived_form_matches_same_carrier_eh_flat_metric
    (p : CoordinatePoint) (z : SREvent) :
    comparisonQuadratic (wickNativeFlatMetric p) (srEventCoordinates z) =
      -srOriginalOrderQuadratic z := by
  rw [original_eh_native_flat_value,sr_original_order_quadratic_computed,EuclideanSpace.norm_sq_eq]
  norm_num [comparisonQuadratic,srEventCoordinates,metric,Matrix.diagonal,Fin.sum_univ_succ,Real.norm_eq_abs]
  norm_num [Matrix.vecCons,Fin.cons,Fin.cases,Fin.succ,Fin.instOfNat,Fin.ofNat]
  change -(z.1*z.1) + (z.2 0*z.2 0 + (z.2 1*z.2 1 + z.2 2*z.2 2)) =
    (z.2 0)^2 + ((z.2 1)^2 + (z.2 2)^2) - z.1^2
  ring

theorem sr_zero_operand_is_same_flat_metric {Ω : TopologicalSpace.Opens CoordinatePoint}
    (p : CoordinatePoint) : originalEHActMetric (0 : MetricSourceProbe Ω) p = wickNativeFlatMetric p := by
  ext i j
  change wickNativeFlatMetric p i j + tensorEncode (0 : Fin 10 → ℝ) i j = _
  have zeroTensor : tensorEncode (0 : Fin 10 → ℝ) = 0 := map_zero tensorEncodeLinear
  rw [zeroTensor]
  simp

theorem sr_source_derived_form_matches_actual_zero_eh_operand
    {Ω : TopologicalSpace.Opens CoordinatePoint} (p : CoordinatePoint) (z : SREvent) :
    comparisonQuadratic (originalEHActMetric (0 : MetricSourceProbe Ω) p) (srEventCoordinates z) =
      -srOriginalOrderQuadratic z := by
  rw [sr_zero_operand_is_same_flat_metric]
  exact sr_source_derived_form_matches_same_carrier_eh_flat_metric p z

def srCommonFlatOperand (Ω : TopologicalSpace.Opens CoordinatePoint) :
    {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω} :=
  ⟨0,wick_original_metric_neighborhood_zero Ω⟩

#print axioms sr_source_derived_form_matches_actual_zero_eh_operand
end AASCKleinGordon.CanonicalLicensing.SRIntegration
