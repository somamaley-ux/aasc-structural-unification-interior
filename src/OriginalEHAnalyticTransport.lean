import OriginalEHIntegratedTransport

/-! Analytic admission on a specified tensor-related test pair. The input
contains coordinate and regular-Lorentz geometric facts, not an action equality,
integrability bridge, original standing rule, or desired response equation. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory

theorem original_eh_c2_lorentz_pullback (g : MetricField)
    (F : CoordinatePoint → CoordinatePoint) (p : CoordinatePoint)
    (domain : C2LorentzMetricAt g (F p)) (regular : ContDiffAt ℝ 3 F p)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (derivative : HasFDerivAt F B.toContinuousLinearMap p) :
    C2LorentzMetricAt (coordinateMetricPullback g F) p := by
  refine ⟨coordinateMetricPullback_symmetric g domain.1 F,
    c3_metric_pullback_c2_at g F p regular domain.2.1,?_⟩
  obtain ⟨D,hD⟩ := domain.2.2
  refine ⟨D.trans B.symm,?_⟩
  have jac : coordinateJacobian F p = coordinateFrameMatrix B := by
    ext i j
    rw [coordinateJacobian_vector F p derivative.differentiableAt,derivative.fderiv]
    rfl
  have composed : coordinateFrameMatrix (D.trans B.symm) =
      coordinateFrameMatrix B.symm * coordinateFrameMatrix D := by
    ext i j
    rw [coordinateFrameMatrix_mul_apply]
    rfl
  have transInv : (coordinateFrameMatrix B.symm).transpose *
      (coordinateFrameMatrix B).transpose = 1 := by
    rw [← Matrix.transpose_mul,coordinateFrameMatrix_right_inverse,Matrix.transpose_one]
  change (coordinateFrameMatrix (D.trans B.symm)).transpose *
    coordinateMetricPullback g F p * coordinateFrameMatrix (D.trans B.symm) = metric
  rw [composed,coordinateMetricPullback_matrix,jac,Matrix.transpose_mul]
  calc
    _ = (coordinateFrameMatrix D).transpose *
        ((coordinateFrameMatrix B.symm).transpose * (coordinateFrameMatrix B).transpose) *
        g (F p) * (coordinateFrameMatrix B * coordinateFrameMatrix B.symm) *
        coordinateFrameMatrix D := by simp only [Matrix.mul_assoc]
    _ = (coordinateFrameMatrix D).transpose * g (F p) * coordinateFrameMatrix D := by
      rw [transInv,coordinateFrameMatrix_right_inverse,mul_one,mul_one]
    _ = metric := hD

variable {Ω Ω' : TopologicalSpace.Opens CoordinatePoint}

structure EHTransportData (g : MetricField) (h : MetricSourceProbe Ω)
    (h' : MetricSourceProbe Ω') where
  coordinate : CoordinatePoint → CoordinatePoint
  region : coordinate '' (Ω' : Set CoordinatePoint) = (Ω : Set CoordinatePoint)
  injective : Set.InjOn coordinate (Ω' : Set CoordinatePoint)
  derivativeEquiv : CoordinatePoint → CoordinatePoint ≃L[ℝ] CoordinatePoint
  derivative : ∀ p ∈ Ω', HasFDerivAt coordinate (derivativeEquiv p).toContinuousLinearMap p
  regular : ∀ p ∈ Ω', ContDiffAt ℝ 3 coordinate p
  symmetric : MetricFieldSymmetric g
  baseline : ∀ p ∈ Ω, C2LorentzMetricAt g p
  perturbed : ∀ p ∈ Ω, C2LorentzMetricAt (originalEHMetricPerturbation g h) p
  test : ∀ p, originalEHTestTensor (h' p) = (coordinateJacobian coordinate p).transpose *
    originalEHTestTensor (h (coordinate p)) * coordinateJacobian coordinate p

namespace EHTransportData
variable {g : MetricField} {h : MetricSourceProbe Ω} {h' : MetricSourceProbe Ω'}
variable (d : EHTransportData g h h')

theorem target_mem (p : CoordinatePoint) (hp : p ∈ Ω') : d.coordinate p ∈ Ω := by
  change d.coordinate p ∈ (Ω : Set CoordinatePoint)
  rw [← d.region]
  exact Set.mem_image_of_mem _ hp

theorem baseline_nondegenerate (p : CoordinatePoint) (hp : p ∈ Ω') :
    (g (d.coordinate p)).det ≠ 0 := by
  obtain ⟨B,frame⟩ := (d.baseline _ (d.target_mem p hp)).2.2
  exact ne_of_lt (native_lorentz_frame_determinant_negative g _ B frame)

theorem perturbed_nondegenerate (p : CoordinatePoint) (hp : p ∈ Ω') :
    ((originalEHMetricPerturbation g h) (d.coordinate p)).det ≠ 0 := by
  obtain ⟨B,frame⟩ := (d.perturbed _ (d.target_mem p hp)).2.2
  exact ne_of_lt (native_lorentz_frame_determinant_negative _ _ B frame)

theorem source_baseline (p : CoordinatePoint) (hp : p ∈ Ω') :
    C2LorentzMetricAt (coordinateMetricPullback g d.coordinate) p :=
  original_eh_c2_lorentz_pullback g d.coordinate p
    (d.baseline _ (d.target_mem p hp)) (d.regular p hp) (d.derivativeEquiv p) (d.derivative p hp)

theorem source_perturbed (p : CoordinatePoint) (hp : p ∈ Ω') :
    C2LorentzMetricAt
      (originalEHMetricPerturbation (coordinateMetricPullback g d.coordinate) h') p := by
  rw [original_eh_pullback_perturbation g h h' d.coordinate d.test]
  exact original_eh_c2_lorentz_pullback _ d.coordinate p
    (d.perturbed _ (d.target_mem p hp)) (d.regular p hp) (d.derivativeEquiv p) (d.derivative p hp)

theorem integrand_square (κ Λ : ℝ) (p : CoordinatePoint) (hp : p ∈ Ω') :
    originalEHRelativeIntegrand κ Λ (coordinateMetricPullback g d.coordinate) h' p =
      |(d.derivativeEquiv p).toContinuousLinearMap.det| *
        originalEHRelativeIntegrand κ Λ g h (d.coordinate p) := by
  unfold originalEHRelativeIntegrand
  rw [original_eh_pullback_perturbation g h h' d.coordinate d.test,
    original_eh_density_natural κ Λ _ (original_eh_perturbation_symmetric g h d.symmetric)
      d.coordinate p (d.perturbed _ (d.target_mem p hp)).2.1
      (d.perturbed_nondegenerate p hp) (d.regular p hp) (d.derivativeEquiv p) (d.derivative p hp),
    original_eh_density_natural κ Λ g d.symmetric d.coordinate p
      (d.baseline _ (d.target_mem p hp)).2.1 (d.baseline_nondegenerate p hp)
      (d.regular p hp) (d.derivativeEquiv p) (d.derivative p hp),
    original_eh_jacobian_det d.coordinate p (d.derivativeEquiv p) (d.derivative p hp)]
  ring

theorem relative_integrability_iff (κ Λ : ℝ) :
    IntegrableOn (originalEHRelativeIntegrand κ Λ g h) (Ω : Set CoordinatePoint) ↔
      IntegrableOn (originalEHRelativeIntegrand κ Λ (coordinateMetricPullback g d.coordinate) h')
        (Ω' : Set CoordinatePoint) := by
  rw [← d.region,integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    Ω'.isOpen.measurableSet (fun p hp => (d.derivative p hp).hasFDerivWithinAt) d.injective]
  apply integrable_congr
  filter_upwards [ae_restrict_mem Ω'.isOpen.measurableSet] with p hp
  simpa only [smul_eq_mul] using (d.integrand_square κ Λ p hp).symm

theorem finite_use_domain_iff (κ Λ : ℝ) :
    OriginalEHFiniteUseDomain κ Λ g h ↔
      OriginalEHFiniteUseDomain κ Λ (coordinateMetricPullback g d.coordinate) h' := by
  constructor
  · intro admitted
    exact ⟨admitted.1,d.source_baseline,d.source_perturbed,
      (d.relative_integrability_iff κ Λ).mp admitted.2.2.2⟩
  · intro admitted
    exact ⟨admitted.1,d.baseline,d.perturbed,
      (d.relative_integrability_iff κ Λ).mpr admitted.2.2.2⟩

theorem action_square (κ Λ : ℝ) :
    originalEHRelativeAction κ Λ (coordinateMetricPullback g d.coordinate) h' =
      originalEHRelativeAction κ Λ g h :=
  original_eh_relative_action_image_transport κ Λ g h h' d.symmetric d.coordinate
    d.region d.injective d.derivativeEquiv d.derivative d.regular
    (fun p hp => (d.baseline _ (d.target_mem p hp)).2.1)
    (fun p hp => (d.perturbed _ (d.target_mem p hp)).2.1)
    d.baseline_nondegenerate d.perturbed_nondegenerate d.test

/-- Equality of actual optional analytic evaluations, beyond equality of
totalized integrals. The original upstream standing is still not this guard. -/
theorem finite_evaluator_square (κ Λ : ℝ) :
    (originalEHFiniteUse κ Λ (coordinateMetricPullback g d.coordinate) h').2 =
      (originalEHFiniteUse κ Λ g h).2 := by
  classical
  unfold originalEHFiniteUse
  rw [← d.finite_use_domain_iff κ Λ,d.action_square κ Λ]

end EHTransportData
end
end AASCSemanticExhaustion
