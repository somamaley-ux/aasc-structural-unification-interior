import WickLorentzMetricCoordinates

noncomputable section
set_option maxHeartbeats 1500000
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickEncodeMatrixLM : (Fin 10 → ℝ) →ₗ[ℝ] NativeRealMatrix := tensorEncodeLinear

def wickTensorCongruenceLM (B : NativeRealMatrix) : (Fin 10 → ℝ) →ₗ[ℝ] (Fin 10 → ℝ) where
  toFun h := tensorDecode (B.transpose*(wickEncodeMatrixLM h)*B)
  map_add' h k := by
    change tensorDecodeLinear (B.transpose*(wickEncodeMatrixLM (h+k))*B)=_
    rw [map_add, Matrix.mul_add, Matrix.add_mul, map_add]
    rfl
  map_smul' c h := by
    change tensorDecodeLinear (B.transpose*(wickEncodeMatrixLM (c • h))*B)=_
    rw [map_smul, Matrix.mul_smul, Matrix.smul_mul, map_smul]
    rfl

theorem wick_tensor_congruence_encode (B : NativeRealMatrix) (h : Fin 10 → ℝ) :
    tensorEncode (wickTensorCongruenceLM B h)=B.transpose*(wickEncodeMatrixLM h)*B := by
  apply tensor_encode_decode
  have symmetric : (wickEncodeMatrixLM h).transpose=wickEncodeMatrixLM h := by
    ext i j
    exact tensorEncode_symmetric h j i
  have result : (B.transpose*(wickEncodeMatrixLM h)*B).transpose=B.transpose*(wickEncodeMatrixLM h)*B := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, symmetric, Matrix.mul_assoc]
  intro i j
  exact congrFun (congrFun result j) i

def wickAffineCoordinateHomeomorph (b : Spacetime) (L : ProperLorentzTransform) :
    CoordinatePoint ≃ₜ CoordinatePoint where
  toEquiv :=
    { toFun p := wickSpacetimeCoordinates b + properLorentzFourCLE L p
      invFun p := (properLorentzFourCLE L).symm (p-wickSpacetimeCoordinates b)
      left_inv p := by simp
      right_inv p := by simp }
  continuous_toFun := continuous_const.add (properLorentzFourCLE L).continuous
  continuous_invFun := (properLorentzFourCLE L).symm.continuous.comp
    (continuous_id.sub continuous_const)

def wickAffineMetricRegion (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) : Opens CoordinatePoint :=
  ⟨wickAffineCoordinateHomeomorph b L '' (Ω : Set CoordinatePoint),
    (wickAffineCoordinateHomeomorph b L).isOpenMap _ Ω.isOpen⟩

def wickNativeAffineMetricTest (b : Spacetime) (L : ProperLorentzTransform)
    {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) :
    MetricSourceProbe (wickAffineMetricRegion b L Ω) := by
  let C := (wickTensorCongruenceLM (wickLorentzMatrix L⁻¹)).toContinuousLinearMap
  let A := wickAffineCoordinateHomeomorph b L
  refine ⟨fun p => C (H (A.symm p)), ?_, ?_, ?_⟩
  · exact C.contDiff.comp (H.contDiff.comp
      ((properLorentzFourCLE L).symm.contDiff.comp (contDiff_id.sub contDiff_const)))
  · exact (H.hasCompactSupport.comp_homeomorph A.symm).comp_left (map_zero C)
  · intro p hp
    have support := tsupport_comp_subset (map_zero C) (fun q => H (A.symm q)) hp
    change p∈tsupport (H ∘ A.symm) at support
    rw [tsupport_comp_eq_preimage H A.symm] at support
    exact ⟨A.symm p,H.tsupport_subset support,A.apply_symm_apply p⟩

theorem wick_affine_spacetime_coordinates (b : Spacetime) (L : ProperLorentzTransform)
    (x : Spacetime) :
    wickAffineCoordinateHomeomorph b L (wickSpacetimeCoordinates x)=
      wickSpacetimeCoordinates (b+spacetimeLorentzCLE L x) := rfl

theorem wick_native_affine_variation (b : Spacetime) (L : ProperLorentzTransform)
    {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) (x : Spacetime) :
    wickNativeMetricVariation (wickNativeAffineMetricTest b L H) (b+spacetimeLorentzCLE L x)=
      (wickLorentzMatrix L⁻¹).transpose*wickNativeMetricVariation H x*wickLorentzMatrix L⁻¹ := by
  change tensorEncode (wickTensorCongruenceLM (wickLorentzMatrix L⁻¹)
    (H ((wickAffineCoordinateHomeomorph b L).symm
      (wickSpacetimeCoordinates (b+spacetimeLorentzCLE L x)))))=_
  rw [← wick_affine_spacetime_coordinates, Homeomorph.symm_apply_apply,
    wick_tensor_congruence_encode]
  rfl

theorem wick_native_affine_finite_metric (b : Spacetime) (L : ProperLorentzTransform)
    {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) (x : Spacetime) :
    wickOriginalFiniteMetric (wickNativeAffineMetricTest b L H) (b+spacetimeLorentzCLE L x)=
      (wickLorentzMatrix L⁻¹).transpose*wickOriginalFiniteMetric H x*wickLorentzMatrix L⁻¹ := by
  unfold wickOriginalFiniteMetric
  rw [wick_native_affine_variation, Matrix.mul_add, Matrix.add_mul, wick_lorentz_flat_metric]

end AASCKleinGordon
