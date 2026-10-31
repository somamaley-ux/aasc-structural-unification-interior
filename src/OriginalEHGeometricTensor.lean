import OriginalEHEulerResponse
import NativeClockHilbertSourceComponents

/-! Lower the already action-derived regular source density with the same metric
and divide by its actual volume. No Einstein tensor is an input to this map. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff

def originalEHGeometricResponse (κ Λ : ℝ) : MetricFieldResponse := fun g p =>
  (coordinateVolumeDensity g p)⁻¹ • (g p * ((2 : ℝ) • ehComputedBulkDensity κ Λ g p) * g p)

theorem eh_original_geometric_tensor_identified (κ Λ : ℝ) (hk : κ ≠ 0) (g : MetricField)
    (p : CoordinatePoint) (negative : (g p).det < 0) :
    originalEHGeometricResponse κ Λ g p =
      -(1 / κ) • (coordinateRicci g p - (coordinateScalarCurvature g p / 2) • g p + Λ • g p) := by
  have unit : IsUnit (g p).det := isUnit_iff_ne_zero.mpr (ne_of_lt negative)
  have volume : coordinateVolumeDensity g p ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (neg_pos.mpr negative))
  have cancel (Q : Tensor2) : g p * ((g p)⁻¹ * Q * (g p)⁻¹) * g p = Q := by
    simp only [← Matrix.mul_assoc,Matrix.mul_nonsing_inv _ unit,Matrix.one_mul,
      Matrix.nonsing_inv_mul_cancel_right _ _ unit]
  unfold originalEHGeometricResponse ehComputedBulkDensity
  rw [smul_smul,Matrix.mul_smul,Matrix.smul_mul,cancel,smul_smul]
  congr 1
  field_simp [volume,hk]

theorem eh_original_geometric_tensor_density (κ Λ : ℝ) (g : MetricField)
    (sg : MetricFieldSymmetric g) (p : CoordinatePoint) (negative : (g p).det < 0) :
    raisedSourceTensorDensity g (originalEHGeometricResponse κ Λ g) p =
      (2 : ℝ) • ehComputedBulkDensity κ Λ g p := by
  have unit : IsUnit (g p).det := isUnit_iff_ne_zero.mpr (ne_of_lt negative)
  have volume : coordinateVolumeDensity g p ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (neg_pos.mpr negative))
  have symG : (g p).transpose = g p := by ext i j; exact sg p j i
  have symB : (g p)⁻¹.transpose = (g p)⁻¹ := by rw [Matrix.transpose_nonsing_inv,symG]
  have cancel (Q : Tensor2) : (g p)⁻¹ * (g p * Q * g p) * (g p)⁻¹ = Q := by
    simp only [← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ unit,Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ unit]
  ext a b
  rw [show raisedSourceTensorDensity g (originalEHGeometricResponse κ Λ g) p a b =
      coordinateVolumeDensity g p *
        ((g p)⁻¹ * originalEHGeometricResponse κ Λ g p * (g p)⁻¹) a b by
    simp only [raisedSourceTensorDensity,native_raise_source_matrix_identity _ _ symB]]
  unfold originalEHGeometricResponse
  rw [Matrix.mul_smul,Matrix.smul_mul,cancel]
  change coordinateVolumeDensity g p * ((coordinateVolumeDensity g p)⁻¹ *
    ((2 : ℝ) • ehComputedBulkDensity κ Λ g p) a b) = _
  rw [← mul_assoc,mul_inv_cancel₀ volume,one_mul]

variable {Ω : Opens CoordinatePoint}

theorem eh_original_geometric_tensor_represents_action_source (κ Λ : ℝ) (hk : κ ≠ 0)
    (g : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) (i : Fin 10) (φ : ScalarSourceProbe Ω) :
    originalEHEulerResponse κ Λ hk g sg hg negative i φ =
      ∫ p, sourceDensityCoordinates (raisedSourceTensorDensity g (originalEHGeometricResponse κ Λ g)) i p * φ p := by
  rw [eh_original_euler_response_density κ Λ hk g sg hg negative]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  by_cases hp : p ∈ Ω
  · change ehComputedSourceDensity κ Λ g i p * φ p =
      raisedSourceTensorDensity g (originalEHGeometricResponse κ Λ g) p
        (sourceSymmetricPair i).1 (sourceSymmetricPair i).2 * φ p
    rw [eh_original_geometric_tensor_density κ Λ g sg p (negative p hp)]
    congr 1
    fin_cases i <;> rfl
  · have zero : φ p = 0 := by
      by_contra nonzero
      exact hp (φ.tsupport_subset (subset_tsupport φ nonzero))
    simp only [zero,mul_zero]

end
end AASCSemanticExhaustion
