import SRCommonFlatGeometry
import SRScaledBoostHalfTurn
import SRNativeConeTopology

/-! SR 6.1: exact receipt of the entire original completed cone forces
conformal geometry. The nine finite probes are consequences of whole-cone
transport, and the positive clock query follows from transported interior. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open scoped Matrix BigOperators

def srMatrixFrameLinear (A : ComparisonMatrixˣ) : CoordinatePoint ≃ₗ[ℝ] CoordinatePoint :=
  (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv

theorem sr_matrix_frame_linear_apply (A : ComparisonMatrixˣ) (v : CoordinatePoint) :
    srMatrixFrameLinear A v = (A : ComparisonMatrix).mulVec v := rfl

def srMatrixFrameEventLinear (A : ComparisonMatrixˣ) : SREvent ≃ₗ[ℝ] SREvent :=
  (srEventCoordinates.trans (srMatrixFrameLinear A)).trans srEventCoordinates.symm

def srMatrixFrameEvent (A : ComparisonMatrixˣ) : SREvent ≃ₜ SREvent :=
  (srMatrixFrameEventLinear A).toContinuousLinearEquiv.toHomeomorph

theorem sr_event_frame_coordinate_square (A : ComparisonMatrixˣ) (z : SREvent) :
    srEventCoordinates (srMatrixFrameEvent A z) =
      (A : ComparisonMatrix).mulVec (srEventCoordinates z) := by
  change srEventCoordinates (srEventCoordinates.symm (srMatrixFrameLinear A (srEventCoordinates z))) = _
  rw [srEventCoordinates.apply_symm_apply,sr_matrix_frame_linear_apply]

theorem sr_coordinate_unit_quadratic_is_source_form (z : SREvent) :
    comparisonQuadratic comparisonUnitLorentz (srEventCoordinates z) = z.1^2-‖z.2‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  norm_num [comparisonQuadratic,comparisonUnitLorentz,srEventCoordinates,Matrix.diagonal,
    Fin.sum_univ_succ,Real.norm_eq_abs]
  change z.1*z.1 + (-(z.2 0*z.2 0) + (-(z.2 1*z.2 1) + -(z.2 2*z.2 2))) =
    z.1^2 - ((z.2 0)^2 + ((z.2 1)^2+(z.2 2)^2))
  ring

theorem sr_original_finite_probe_is_null (i : Fin 10) (nonclock : i ≠ 0) :
    comparisonQuadratic comparisonUnitLorentz (originalComparisonProbe i) = 0 := by
  have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  fin_cases i <;>
    norm_num [comparisonQuadratic,comparisonUnitLorentz,originalComparisonProbe,
      Matrix.diagonal,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.vecHead,Matrix.vecTail] at *

theorem sr_original_finite_probe_is_native_boundary (i : Fin 10) (nonclock : i ≠ 0) :
    ‖(srEventCoordinates.symm (originalComparisonProbe i)).2‖ =
      (srEventCoordinates.symm (originalComparisonProbe i)).1 := by
  have hq := sr_coordinate_unit_quadratic_is_source_form
    (srEventCoordinates.symm (originalComparisonProbe i))
  rw [srEventCoordinates.apply_symm_apply,sr_original_finite_probe_is_null i nonclock] at hq
  have ht : 0 ≤ (srEventCoordinates.symm (originalComparisonProbe i)).1 := by
    fin_cases i <;> norm_num [srEventCoordinates,originalComparisonProbe,Real.sqrt_nonneg]
  nlinarith [norm_nonneg (srEventCoordinates.symm (originalComparisonProbe i)).2]

theorem sr_exact_completed_cone_frame_has_null_probe_answers (A : ComparisonMatrixˣ)
    (sourceCone : srMatrixFrameEvent A '' srRayFutureCone = srRayFutureCone) :
    ∀ i : Fin 10, i ≠ 0 →
      comparisonQuadratic comparisonUnitLorentz
        ((A : ComparisonMatrix).mulVec (originalComparisonProbe i)) = 0 := by
  intro i hi
  let z := srEventCoordinates.symm (originalComparisonProbe i)
  have boundary := sr_exact_original_cone_frame_preserves_boundary
    (srMatrixFrameEvent A) sourceCone z (sr_original_finite_probe_is_native_boundary i hi)
  have h := sr_coordinate_unit_quadratic_is_source_form (srMatrixFrameEvent A z)
  rw [sr_event_frame_coordinate_square] at h
  have original : srEventCoordinates z = originalComparisonProbe i := srEventCoordinates.apply_symm_apply _
  rw [original] at h
  exact h.trans (by rw [boundary];ring)

theorem sr_exact_completed_cone_frame_has_positive_clock_answer (A : ComparisonMatrixˣ)
    (sourceCone : srMatrixFrameEvent A '' srRayFutureCone = srRayFutureCone) :
    0 < comparisonAnswers (srFramePullback (A : ComparisonMatrix)) 0 := by
  have transported := sr_exact_original_cone_frame_preserves_strict_clock_body
    (srMatrixFrameEvent A) sourceCone (1,0) (by norm_num)
  change 0 < comparisonQuadratic (srFramePullback (A : ComparisonMatrix)) (originalComparisonProbe 0)
  rw [sr_frame_pullback_quadratic]
  have initial : srEventCoordinates (1,0) = originalComparisonProbe 0 := rfl
  have hq' := sr_coordinate_unit_quadratic_is_source_form (srMatrixFrameEvent A (1,0))
  rw [sr_event_frame_coordinate_square,initial] at hq'
  rw [hq']
  change ‖(srMatrixFrameEvent A (1,0)).2‖ < (srMatrixFrameEvent A (1,0)).1 at transported
  nlinarith [norm_nonneg (srMatrixFrameEvent A (1,0)).2]

theorem sr_exact_completed_source_cone_constructs_positive_conformal_frame (A : ComparisonMatrixˣ)
    (sourceCone : srMatrixFrameEvent A '' srRayFutureCone = srRayFutureCone) :
    ∃ κ : ℝ, 0 < κ ∧ srFramePullback (A : ComparisonMatrix) = κ • comparisonUnitLorentz := by
  let κ := comparisonAnswers (srFramePullback (A : ComparisonMatrix)) 0
  refine ⟨κ,sr_exact_completed_cone_frame_has_positive_clock_answer A sourceCone,?_⟩
  have null : ∀ i : Fin 10, i ≠ 0 → comparisonAnswers (srFramePullback (A : ComparisonMatrix)) i = 0 := by
    intro i hi
    exact (sr_frame_pullback_quadratic _ _).trans
      (sr_exact_completed_cone_frame_has_null_probe_answers A sourceCone i hi)
  have h := reconstruct_null_answers (comparisonAnswers (srFramePullback (A : ComparisonMatrix))) null
  rw [comparison_reconstruction_recovers_every_symmetric_receipt _ (sr_frame_pullback_symmetric _)] at h
  exact h

#print axioms sr_exact_completed_source_cone_constructs_positive_conformal_frame
end AASCKleinGordon.CanonicalLicensing.SRIntegration
