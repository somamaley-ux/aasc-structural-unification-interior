import FourDimensionalMetricResponse
import OriginalEHGeometricCore
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The bounded action-derived response supplies an actual smooth witness
for the independent differential comparison. Its first-response law has
already been proved by varying the specified action. -/
namespace AASCSemanticExhaustion
noncomputable section
open scoped Matrix.Norms.Elementwise

theorem differentiable_profile_and_div2_of_original_affinity
    (E : MetricFieldResponse) (h : OriginalCurvatureFirstResponse E) :
    ContDiff ℝ ⊤ (metricHessianResponseAt E 0) ∧
    Differentiable ℝ (metricHessianResponseAt E 0) ∧
    Differentiable ℝ (fderiv ℝ (metricHessianResponseAt E 0)) ∧
    NormalResponseSecondSymmetries E := by
  let F := metricHessianResponseAt E 0
  have aff : HessianAffine F := metric_response_hessian_affine_from_first_response E
    (original_curvature_first_response_derives_metric_affinity E h)
  let L : metricHessianSpace →ₗ[ℝ] Tensor2 :=
    { toFun := fun H => F H - F 0
      map_add' := by intro H K; rw [aff.1]; abel
      map_smul' := by intro r H; rw [aff.2]; simp }
  let A := L.toContinuousLinearMap
  have rep : F = fun H => F 0 + A H := by
    funext H
    change F H = F 0 + (F H - F 0)
    abel
  have hfd (H : metricHessianSpace) : HasFDerivAt F A H := by
    nth_rw 1 [rep]
    simpa using (A.hasFDerivAt.const_add (F 0) : HasFDerivAt _ _ H)
  have slope : fderiv ℝ F = fun _ => A := funext fun H => (hfd H).fderiv
  refine ⟨?_, fun H => (hfd H).differentiableAt, ?_, ?_⟩
  · change ContDiff ℝ ⊤ F
    rw [rep]
    exact contDiff_const.add A.contDiff
  · change Differentiable ℝ (fderiv ℝ F)
    rw [slope]
    exact differentiable_const _
  · intro H
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro _ _ _ _ _ _
      norm_num
    · intro U V i j
      change (fderiv ℝ (fderiv ℝ F) H U V) i j = _
      rw [slope, (hasFDerivAt_const A H).fderiv]
      simp [normalResponseSecondContraction]

theorem occupied_einstein_hilbert_has_smooth_profile_and_div2
    (κ Λ : ℝ) (hk : κ ≠ 0) :
    ContDiff ℝ ⊤ (metricHessianResponseAt (originalEHGeometricResponse κ Λ) 0) ∧
    Differentiable ℝ (metricHessianResponseAt (originalEHGeometricResponse κ Λ) 0) ∧
    Differentiable ℝ (fderiv ℝ (metricHessianResponseAt (originalEHGeometricResponse κ Λ) 0)) ∧
    NormalResponseSecondSymmetries (originalEHGeometricResponse κ Λ) :=
  differentiable_profile_and_div2_of_original_affinity _
    (eh_original_geometric_curvature_first_response κ Λ hk)

end
end AASCSemanticExhaustion
