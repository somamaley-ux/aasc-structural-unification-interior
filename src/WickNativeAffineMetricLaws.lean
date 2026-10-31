import WickNativeAffineMetricTests

noncomputable section
set_option maxHeartbeats 1500000
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem wick_real_metric_congruence_injective (B : NativeRealMatrix) (detB : B.det=1)
    (X Y : NativeRealMatrix) (same : B.transpose*X*B=B.transpose*Y*B) : X=Y := by
  have unit : IsUnit B.det := by rw [detB]; exact isUnit_one
  have transunit : IsUnit B.transpose.det := by rwa [Matrix.det_transpose]
  have recover (Z : NativeRealMatrix) : B.transpose⁻¹*(B.transpose*Z*B)*B⁻¹=Z := by
    simp only [← Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul B.transpose transunit, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv B unit, Matrix.mul_one]
  exact (recover X).symm.trans
    ((congrArg (fun Z => B.transpose⁻¹*Z*B⁻¹) same).trans (recover Y))

theorem wick_native_affine_test_injective (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) : Function.Injective
      (wickNativeAffineMetricTest b L : MetricSourceProbe Ω → MetricSourceProbe (wickAffineMetricRegion b L Ω)) := by
  intro H K same
  apply TestFunction.ext
  intro p
  have evaluated := congrArg (fun J : MetricSourceProbe (wickAffineMetricRegion b L Ω) =>
    J (wickAffineCoordinateHomeomorph b L p)) same
  change wickTensorCongruenceLM (wickLorentzMatrix L⁻¹)
    (H ((wickAffineCoordinateHomeomorph b L).symm (wickAffineCoordinateHomeomorph b L p))) =
      wickTensorCongruenceLM (wickLorentzMatrix L⁻¹)
        (K ((wickAffineCoordinateHomeomorph b L).symm (wickAffineCoordinateHomeomorph b L p))) at evaluated
  rw [Homeomorph.symm_apply_apply] at evaluated
  have encoded := congrArg tensorEncode evaluated
  rw [wick_tensor_congruence_encode, wick_tensor_congruence_encode] at encoded
  have recovered := wick_real_metric_congruence_injective _ (wick_lorentz_matrix_det L⁻¹) _ _ encoded
  have decoded := congrArg tensorDecode recovered
  change tensorDecode (tensorEncode (H p))=tensorDecode (tensorEncode (K p)) at decoded
  simpa only [tensor_decode_encode] using decoded

theorem wick_native_affine_test_smul (b : Spacetime) (L : ProperLorentzTransform)
    {Ω : Opens CoordinatePoint} (r : ℝ) (H : MetricSourceProbe Ω) :
    wickNativeAffineMetricTest b L (r • H)=r • wickNativeAffineMetricTest b L H := by
  apply TestFunction.ext
  intro p
  exact (wickTensorCongruenceLM (wickLorentzMatrix L⁻¹)).map_smul r _

theorem wick_native_affine_test_add (b : Spacetime) (L : ProperLorentzTransform)
    {Ω : Opens CoordinatePoint} (H K : MetricSourceProbe Ω) :
    wickNativeAffineMetricTest b L (H+K)=wickNativeAffineMetricTest b L H+wickNativeAffineMetricTest b L K := by
  apply TestFunction.ext
  intro p
  exact (wickTensorCongruenceLM (wickLorentzMatrix L⁻¹)).map_add _ _

def wickTransportedMetricDomain (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) : Set (MetricSourceProbe (wickAffineMetricRegion b L Ω)) :=
  wickNativeAffineMetricTest b L '' wickOriginalMetricNeighborhood Ω

theorem wick_transported_metric_domain_exact (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω) :
    wickNativeAffineMetricTest b L H ∈ wickTransportedMetricDomain b L Ω ↔
      H∈wickOriginalMetricNeighborhood Ω := by
  constructor
  · rintro ⟨K,inside,same⟩
    exact (wick_native_affine_test_injective b L Ω same) ▸ inside
  · intro inside
    exact ⟨H,inside,rfl⟩

theorem wick_native_affine_metric_determinant (b : Spacetime) (L : ProperLorentzTransform)
    {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) (x : Spacetime) :
    (wickOriginalFiniteMetric (wickNativeAffineMetricTest b L H) (b+spacetimeLorentzCLE L x)).det =
      (wickOriginalFiniteMetric H x).det := by
  rw [wick_native_affine_finite_metric]
  simp only [Matrix.det_mul, Matrix.det_transpose, wick_lorentz_matrix_det, one_mul, mul_one]

end AASCKleinGordon
