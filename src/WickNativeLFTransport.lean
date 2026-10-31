import WickLFAffinePullback

noncomputable section
set_option maxHeartbeats 1500000
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem wick_affine_region_maps (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) : Set.MapsTo
    (wickLFAffineHomeomorph (wickSpacetimeCoordinates b) (properLorentzFourCLE L))
      Ω (wickAffineMetricRegion b L Ω) := by
  intro x hx
  exact ⟨x,hx,rfl⟩

def wickNativeAffineMetricTestCLM (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) : MetricSourceProbe Ω →L[ℝ]
      MetricSourceProbe (wickAffineMetricRegion b L Ω) :=
  (TestFunction.postcompCLM (wickTensorCongruenceLM (wickLorentzMatrix L⁻¹)).toContinuousLinearMap).comp
    (wickAffinePullTestCLM (wickSpacetimeCoordinates b) (properLorentzFourCLE L)
      (wick_affine_region_maps b L Ω))

theorem wick_native_affine_clm_eq (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) :
    (wickNativeAffineMetricTestCLM b L Ω : MetricSourceProbe Ω →
      MetricSourceProbe (wickAffineMetricRegion b L Ω))=wickNativeAffineMetricTest b L := by
  funext H
  apply TestFunction.ext
  intro x
  rfl

theorem wick_native_affine_test_continuous (b : Spacetime)
    (L : ProperLorentzTransform) (Ω : Opens CoordinatePoint) :
    Continuous (wickNativeAffineMetricTest b L : MetricSourceProbe Ω →
      MetricSourceProbe (wickAffineMetricRegion b L Ω)) := by
  rw [← wick_native_affine_clm_eq]
  exact (wickNativeAffineMetricTestCLM b L Ω).continuous

theorem wick_lorentz_matrix_mul (L M : ProperLorentzTransform) :
    wickLorentzMatrix (L*M)=wickLorentzMatrix L*wickLorentzMatrix M := by
  exact LinearMap.toMatrix'_comp L.val.toLinearMap M.val.toLinearMap

theorem wick_lorentz_matrix_one : wickLorentzMatrix 1=1 := LinearMap.toMatrix'_id

theorem wick_tensor_congruence_comp (A B : NativeRealMatrix) (h : Fin 10 → ℝ) :
    wickTensorCongruenceLM A (wickTensorCongruenceLM B h)=wickTensorCongruenceLM (B*A) h := by
  change tensorDecode (A.transpose*(wickEncodeMatrixLM (wickTensorCongruenceLM B h))*A)=_
  have encoded : wickEncodeMatrixLM (wickTensorCongruenceLM B h)=B.transpose*wickEncodeMatrixLM h*B :=
    wick_tensor_congruence_encode B h
  rw [encoded]
  change tensorDecode (A.transpose*(B.transpose*wickEncodeMatrixLM h*B)*A)=
    tensorDecode ((B*A).transpose*wickEncodeMatrixLM h*(B*A))
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

theorem wick_tensor_congruence_one (h : Fin 10 → ℝ) : wickTensorCongruenceLM 1 h=h := by
  change tensorDecode ((1 : NativeRealMatrix).transpose*wickEncodeMatrixLM h*1)=h
  simpa only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] using tensor_decode_encode h

theorem wick_affine_inverse_region_maps (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) : Set.MapsTo
    (wickLFAffineHomeomorph (-(properLorentzFourCLE L).symm (wickSpacetimeCoordinates b))
      (properLorentzFourCLE L).symm) (wickAffineMetricRegion b L Ω) Ω := by
  rintro _ ⟨x,hx,rfl⟩
  change -(properLorentzFourCLE L).symm (wickSpacetimeCoordinates b)+
    (properLorentzFourCLE L).symm (wickSpacetimeCoordinates b+properLorentzFourCLE L x)∈Ω
  simpa only [map_add, ContinuousLinearEquiv.symm_apply_apply, neg_add_cancel_left] using hx

def wickNativeAffineMetricInverseCLM (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) : MetricSourceProbe (wickAffineMetricRegion b L Ω) →L[ℝ]
      MetricSourceProbe Ω :=
  (TestFunction.postcompCLM (wickTensorCongruenceLM (wickLorentzMatrix L)).toContinuousLinearMap).comp
    (wickAffinePullTestCLM (-(properLorentzFourCLE L).symm (wickSpacetimeCoordinates b))
      (properLorentzFourCLE L).symm (wick_affine_inverse_region_maps b L Ω))

theorem wick_native_affine_inverse_apply (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) (J : MetricSourceProbe (wickAffineMetricRegion b L Ω))
    (x : CoordinatePoint) : wickNativeAffineMetricInverseCLM b L Ω J x=
      wickTensorCongruenceLM (wickLorentzMatrix L) (J (wickAffineCoordinateHomeomorph b L x)) := by
  change wickTensorCongruenceLM (wickLorentzMatrix L)
    (J ((properLorentzFourCLE L) (x-(-(properLorentzFourCLE L).symm (wickSpacetimeCoordinates b)))))=_
  simp only [sub_neg_eq_add, map_add, ContinuousLinearEquiv.apply_symm_apply]
  congr 2
  exact add_comm _ _

theorem wick_native_affine_inverse_left (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω) :
    wickNativeAffineMetricInverseCLM b L Ω (wickNativeAffineMetricTest b L H)=H := by
  apply TestFunction.ext
  intro x
  rw [wick_native_affine_inverse_apply]
  change wickTensorCongruenceLM (wickLorentzMatrix L)
    (wickTensorCongruenceLM (wickLorentzMatrix L⁻¹)
      (H ((wickAffineCoordinateHomeomorph b L).symm (wickAffineCoordinateHomeomorph b L x))))=H x
  rw [Homeomorph.symm_apply_apply,wick_tensor_congruence_comp,
    ← wick_lorentz_matrix_mul, inv_mul_cancel, wick_lorentz_matrix_one,wick_tensor_congruence_one]

theorem wick_native_affine_inverse_right (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) (J : MetricSourceProbe (wickAffineMetricRegion b L Ω)) :
    wickNativeAffineMetricTest b L (wickNativeAffineMetricInverseCLM b L Ω J)=J := by
  apply TestFunction.ext
  intro x
  change wickTensorCongruenceLM (wickLorentzMatrix L⁻¹)
    (wickNativeAffineMetricInverseCLM b L Ω J ((wickAffineCoordinateHomeomorph b L).symm x))=J x
  rw [wick_native_affine_inverse_apply,Homeomorph.apply_symm_apply,wick_tensor_congruence_comp,
    ← wick_lorentz_matrix_mul, mul_inv_cancel, wick_lorentz_matrix_one,wick_tensor_congruence_one]

def wickNativeAffineMetricTestCLE (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) : MetricSourceProbe Ω ≃L[ℝ]
      MetricSourceProbe (wickAffineMetricRegion b L Ω) where
  toLinearEquiv :=
    { toLinearMap := (wickNativeAffineMetricTestCLM b L Ω).toLinearMap
      invFun := wickNativeAffineMetricInverseCLM b L Ω
      left_inv H := by
        change wickNativeAffineMetricInverseCLM b L Ω (wickNativeAffineMetricTestCLM b L Ω H)=H
        rw [show wickNativeAffineMetricTestCLM b L Ω H=wickNativeAffineMetricTest b L H from
          congrFun (wick_native_affine_clm_eq b L Ω) H]
        exact wick_native_affine_inverse_left b L Ω H
      right_inv J := by
        change wickNativeAffineMetricTestCLM b L Ω (wickNativeAffineMetricInverseCLM b L Ω J)=J
        rw [show wickNativeAffineMetricTestCLM b L Ω (wickNativeAffineMetricInverseCLM b L Ω J)=
          wickNativeAffineMetricTest b L (wickNativeAffineMetricInverseCLM b L Ω J) from
          congrFun (wick_native_affine_clm_eq b L Ω) _]
        exact wick_native_affine_inverse_right b L Ω J }
  continuous_toFun := (wickNativeAffineMetricTestCLM b L Ω).continuous
  continuous_invFun := (wickNativeAffineMetricInverseCLM b L Ω).continuous

theorem wick_transported_metric_domain_open (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) : IsOpen (wickTransportedMetricDomain b L Ω) := by
  change IsOpen (wickNativeAffineMetricTest b L '' wickOriginalMetricNeighborhood Ω)
  rw [← wick_native_affine_clm_eq]
  exact (wickNativeAffineMetricTestCLE b L Ω).toHomeomorph.isOpenMap _
    (wick_original_metric_neighborhood_open Ω)

end AASCKleinGordon
