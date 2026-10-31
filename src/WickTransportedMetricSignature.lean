import WickNativeAffineMetricLaws

noncomputable section
set_option maxHeartbeats 1500000
open scoped BigOperators
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

/-- Signature independent of which coordinate vector is used as time pivot.
The original chart's stronger negative-00 Schur witness supplies this. -/
def WickIntrinsicLorentzSignature (G : NativeRealMatrix) : Prop :=
  ∃ c : ℝ,c<0 ∧
  ∃ e : (Fin 4 → ℝ) ≃ₗ[ℝ] ℝ × (Fin 3 → ℝ),
  ∃ A : Matrix (Fin 3) (Fin 3) ℝ,
    (∀ i j,A i j=A j i) ∧
    (∀ x : Fin 3 → ℝ,x≠0 → 0<wickMatrixQuadratic A x) ∧
    ∀ v,wickMatrixQuadratic G v=c*(e v).1^2+wickMatrixQuadratic A (e v).2

theorem wick_original_signature_is_intrinsic (G : NativeRealMatrix)
    (signature : WickLorentzSignature G) : WickIntrinsicLorentzSignature G := by
  obtain ⟨e,A,negative,symmetric,positive,quadratic⟩ := signature
  exact ⟨G 0 0,negative,e,A,symmetric,positive,quadratic⟩

theorem wick_matrix_quadratic_eq_dot (G : NativeRealMatrix) (v : Fin 4 → ℝ) :
    wickMatrixQuadratic G v=dotProduct v (Matrix.mulVec G v) := by
  simp only [wickMatrixQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem wick_matrix_quadratic_congruence (G B : NativeRealMatrix) (v : Fin 4 → ℝ) :
    wickMatrixQuadratic (B.transpose*G*B) v=wickMatrixQuadratic G (Matrix.mulVec B v) := by
  calc
    _=dotProduct v (Matrix.mulVec B.transpose (Matrix.mulVec G (Matrix.mulVec B v))) := by
      rw [wick_matrix_quadratic_eq_dot]
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _=dotProduct (Matrix.mulVec B v) (Matrix.mulVec G (Matrix.mulVec B v)) := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _=_ := (wick_matrix_quadratic_eq_dot _ _).symm

theorem wick_intrinsic_signature_lorentz (G : NativeRealMatrix)
    (signature : WickIntrinsicLorentzSignature G) (L : ProperLorentzTransform) :
    WickIntrinsicLorentzSignature ((wickLorentzMatrix L⁻¹).transpose*G*wickLorentzMatrix L⁻¹) := by
  obtain ⟨c,negative,e,A,symmetric,positive,quadratic⟩ := signature
  refine ⟨c,negative,(properLorentzFourCLE L⁻¹).toLinearEquiv.trans e,A,
    symmetric,positive,?_⟩
  intro v
  rw [wick_matrix_quadratic_congruence]
  change wickMatrixQuadratic G (Matrix.mulVec (LinearMap.toMatrix' (L⁻¹).val.toLinearMap) v)=_
  rw [LinearMap.toMatrix'_mulVec]
  exact quadratic _

theorem wick_transported_metric_signature (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) (J : MetricSourceProbe (wickAffineMetricRegion b L Ω))
    (inside : J∈wickTransportedMetricDomain b L Ω) (y : Spacetime) :
    WickIntrinsicLorentzSignature (wickOriginalFiniteMetric J y) ∧
      (wickOriginalFiniteMetric J y).det≠0 := by
  obtain ⟨H,admitted,rfl⟩ := inside
  let x := (spacetimeLorentzCLE L).symm (y-b)
  have recover : b+spacetimeLorentzCLE L x=y := by
    simp only [x, ContinuousLinearEquiv.apply_symm_apply]
    abel
  rw [← recover, wick_native_affine_finite_metric]
  constructor
  · exact wick_intrinsic_signature_lorentz _
      (wick_original_signature_is_intrinsic _ (wick_original_metric_domain_fixed_signature Ω H admitted x)) L
  · simpa only [Matrix.det_mul, Matrix.det_transpose, wick_lorentz_matrix_det,
      one_mul, mul_one] using wick_original_metric_domain_nondegenerate Ω H admitted x

end AASCKleinGordon
