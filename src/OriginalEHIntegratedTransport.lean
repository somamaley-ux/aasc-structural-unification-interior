import OriginalEHGeometricCore
import Mathlib.MeasureTheory.Function.Jacobian

/-! Integrated transport of the independently fixed original action density.
The coordinate map, its actual derivative and the transported region enter
the change-of-variables theorem. No integral agreement is assumed. The test
version retains the exact tensor pullback equation as an operand hypothesis;
construction of a bundled transported test and original standing is separate.
-/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory

/-- Matrix-typed view of the accepted ten-coordinate encoding. -/
def originalEHTestTensor (v : Fin 10 → ℝ) : Tensor2 := tensorEncode v

theorem original_eh_jacobian_det (F : CoordinatePoint → CoordinatePoint)
    (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (derivative : HasFDerivAt F B.toContinuousLinearMap p) :
    (coordinateJacobian F p).det = B.toContinuousLinearMap.det := by
  change (coordinateJacobian F p).det = LinearMap.det B.toLinearMap
  rw [← LinearMap.det_toMatrix']
  congr 1
  ext i j
  rw [coordinateJacobian_vector F p derivative.differentiableAt,derivative.fderiv]
  rfl

theorem original_eh_integrated_relative_density_transport
    (κ Λ : ℝ) (g k : MetricField) (sg : MetricFieldSymmetric g)
    (sk : MetricFieldSymmetric k) (F : CoordinatePoint → CoordinatePoint)
    (s : Set CoordinatePoint) (hs : MeasurableSet s) (injective : Set.InjOn F s)
    (B : CoordinatePoint → CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (derivative : ∀ p ∈ s, HasFDerivAt F (B p).toContinuousLinearMap p)
    (regularF : ∀ p ∈ s, ContDiffAt ℝ 3 F p)
    (regularG : ∀ p ∈ s, ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) (F p))
    (regularK : ∀ p ∈ s, ∀ a b, ContDiffAt ℝ 2 (fun x => k x a b) (F p))
    (nondegenerateG : ∀ p ∈ s, (g (F p)).det ≠ 0)
    (nondegenerateK : ∀ p ∈ s, (k (F p)).det ≠ 0) :
    (∫ y in F '' s, originalEHScalarDensity κ Λ k y - originalEHScalarDensity κ Λ g y) =
      ∫ x in s, originalEHScalarDensity κ Λ (coordinateMetricPullback k F) x -
        originalEHScalarDensity κ Λ (coordinateMetricPullback g F) x := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (fun p hp => (derivative p hp).hasFDerivWithinAt) injective]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hs] with p hp
  rw [original_eh_density_natural κ Λ k sk F p (regularK p hp)
    (nondegenerateK p hp) (regularF p hp) (B p) (derivative p hp),
    original_eh_density_natural κ Λ g sg F p (regularG p hp)
    (nondegenerateG p hp) (regularF p hp) (B p) (derivative p hp),
    original_eh_jacobian_det F p (B p) (derivative p hp)]
  simp only [smul_eq_mul,mul_sub]

theorem original_eh_pullback_perturbation
    {Ω Ω' : TopologicalSpace.Opens CoordinatePoint}
    (g : MetricField) (h : MetricSourceProbe Ω) (h' : MetricSourceProbe Ω')
    (F : CoordinatePoint → CoordinatePoint)
    (test : ∀ p, originalEHTestTensor (h' p) =
      (coordinateJacobian F p).transpose * originalEHTestTensor (h (F p)) * coordinateJacobian F p) :
    originalEHMetricPerturbation (coordinateMetricPullback g F) h' =
      coordinateMetricPullback (originalEHMetricPerturbation g h) F := by
  funext p
  change (coordinateMetricPullback g F p + originalEHTestTensor (h' p) : Tensor2) =
    (coordinateMetricPullback (originalEHMetricPerturbation g h) F p : Tensor2)
  rw [coordinateMetricPullback_matrix,test,coordinateMetricPullback_matrix]
  change _ = (coordinateJacobian F p).transpose *
    (g (F p) + originalEHTestTensor (h (F p))) * coordinateJacobian F p
  rw [Matrix.mul_add,Matrix.add_mul]

theorem original_eh_perturbation_symmetric
    {Ω : TopologicalSpace.Opens CoordinatePoint}
    (g : MetricField) (h : MetricSourceProbe Ω) (sg : MetricFieldSymmetric g) :
    MetricFieldSymmetric (originalEHMetricPerturbation g h) := by
  intro p a b
  change g p a b + tensorEncode (h p) a b = g p b a + tensorEncode (h p) b a
  rw [sg p a b,tensorEncode_symmetric]

/-- The integrals are those of the same original finite metric action, on
the actual image region and the supplied pair of tensor-related compact tests.
No original standing rule occurs as a coordinate-defined predicate. -/
theorem original_eh_relative_action_image_transport
    {Ω Ω' : TopologicalSpace.Opens CoordinatePoint}
    (κ Λ : ℝ) (g : MetricField) (h : MetricSourceProbe Ω) (h' : MetricSourceProbe Ω')
    (sg : MetricFieldSymmetric g) (F : CoordinatePoint → CoordinatePoint)
    (region : F '' (Ω' : Set CoordinatePoint) = (Ω : Set CoordinatePoint))
    (injective : Set.InjOn F (Ω' : Set CoordinatePoint))
    (B : CoordinatePoint → CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (derivative : ∀ p ∈ Ω', HasFDerivAt F (B p).toContinuousLinearMap p)
    (regularF : ∀ p ∈ Ω', ContDiffAt ℝ 3 F p)
    (regularG : ∀ p ∈ Ω', ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) (F p))
    (regularK : ∀ p ∈ Ω', ∀ a b,
      ContDiffAt ℝ 2 (fun x => originalEHMetricPerturbation g h x a b) (F p))
    (nondegenerateG : ∀ p ∈ Ω', (g (F p)).det ≠ 0)
    (nondegenerateK : ∀ p ∈ Ω', ((originalEHMetricPerturbation g h) (F p)).det ≠ 0)
    (test : ∀ p, originalEHTestTensor (h' p) =
      (coordinateJacobian F p).transpose * originalEHTestTensor (h (F p)) * coordinateJacobian F p) :
    originalEHRelativeAction κ Λ (coordinateMetricPullback g F) h' =
      originalEHRelativeAction κ Λ g h := by
  unfold originalEHRelativeAction originalEHRelativeIntegrand
  rw [original_eh_pullback_perturbation g h h' F test]
  have transported := original_eh_integrated_relative_density_transport κ Λ g
    (originalEHMetricPerturbation g h) sg (original_eh_perturbation_symmetric g h sg)
    F (Ω' : Set CoordinatePoint) Ω'.isOpen.measurableSet injective B derivative
    regularF regularG regularK nondegenerateG nondegenerateK
  rw [region] at transported
  exact transported.symm

end
end AASCSemanticExhaustion
