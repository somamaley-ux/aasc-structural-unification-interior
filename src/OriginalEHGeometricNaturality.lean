import OriginalEHGeometricTensor

namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Topology

theorem eh_pullback_determinant_negative (g : MetricField)
    (F : CoordinatePoint → CoordinatePoint) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (derivative : HasFDerivAt F B.toContinuousLinearMap p)
    (negative : (g (F p)).det < 0) :
    (coordinateMetricPullback g F p).det < 0 := by
  have jac : coordinateJacobian F p = coordinateFrameMatrix B := by
    ext i j
    rw [coordinateJacobian_vector F p derivative.differentiableAt,derivative.fderiv]
    rfl
  have nonzero : (coordinateFrameMatrix B).det ≠ 0 := by
    have hi := congrArg Matrix.det (coordinateFrameMatrix_right_inverse B)
    simp only [Matrix.det_mul,Matrix.det_one] at hi
    intro zero
    rw [zero,zero_mul] at hi
    norm_num at hi
  rw [coordinateMetricPullback_matrix,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,jac]
  rw [show (coordinateFrameMatrix B).det * (g (F p)).det * (coordinateFrameMatrix B).det =
    (coordinateFrameMatrix B).det ^ 2 * (g (F p)).det by ring]
  exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero nonzero) negative

theorem eh_original_geometric_tensor_natural (κ Λ : ℝ) (hk : κ ≠ 0)
    (g : MetricField) (sg : MetricFieldSymmetric g)
    (F : CoordinatePoint → CoordinatePoint) (p : CoordinatePoint)
    (regularG : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) (F p))
    (negative : (g (F p)).det < 0) (regularF : ContDiffAt ℝ 3 F p)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (derivative : HasFDerivAt F B.toContinuousLinearMap p) :
    originalEHGeometricResponse κ Λ (coordinateMetricPullback g F) p =
      (coordinateJacobian F p).transpose * originalEHGeometricResponse κ Λ g (F p) *
        coordinateJacobian F p := by
  rw [eh_original_geometric_tensor_identified κ Λ hk _ p
    (eh_pullback_determinant_negative g F p B derivative negative),
    eh_original_geometric_tensor_identified κ Λ hk g (F p) negative,
    coordinate_ricci_regular_natural g sg F p regularG (ne_of_lt negative) regularF B derivative,
    coordinate_scalar_regular_natural g sg F p regularG (ne_of_lt negative) regularF B derivative,
    coordinateMetricPullback_matrix]
  simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.mul_add,Matrix.add_mul]

theorem eh_original_geometric_response_regular_natural (κ Λ : ℝ) (hk : κ ≠ 0) :
    RegularLorentzResponseNatural (originalEHGeometricResponse κ Λ) := by
  intro F p B regularF derivative g domain
  obtain ⟨D,frame⟩ := domain.2.2
  exact eh_original_geometric_tensor_natural κ Λ hk g domain.1 F p domain.2.1
    (native_lorentz_frame_determinant_negative g (F p) D frame)
    (regularF.of_le (by norm_num)) B derivative

theorem eh_original_geometric_response_twojet_local (κ Λ : ℝ) (hk : κ ≠ 0) :
    RegularLorentzTwoJetLocal (originalEHGeometricResponse κ Λ) := by
  intro g h p dg dh equal
  obtain ⟨B,frameG⟩ := dg.2.2
  obtain ⟨D,frameH⟩ := dh.2.2
  have ng := native_lorentz_frame_determinant_negative g p B frameG
  have nh := native_lorentz_frame_determinant_negative h p D frameH
  have curv := c2_general_curvature_twojet_congr g h p dg.1 dh.1 dg.2.1 dh.2.1
    (ne_of_lt ng) (ne_of_lt nh) equal
  have ricci : coordinateRicci g p = coordinateRicci h p := by
    unfold coordinateRicci
    rw [equal.1,curv]
  rw [eh_original_geometric_tensor_identified κ Λ hk g p ng,
    eh_original_geometric_tensor_identified κ Λ hk h p nh]
  simp only [coordinateScalarCurvature,equal.1,ricci]

theorem eh_original_geometric_response_symmetric (κ Λ : ℝ) (hk : κ ≠ 0)
    (g : MetricField) (p : CoordinatePoint) (domain : C2LorentzMetricAt g p) :
    ∀ a b, originalEHGeometricResponse κ Λ g p a b = originalEHGeometricResponse κ Λ g p b a := by
  obtain ⟨B,frame⟩ := domain.2.2
  rw [eh_original_geometric_tensor_identified κ Λ hk g p
    (native_lorentz_frame_determinant_negative g p B frame)]
  intro a b
  change -(1/κ) * (_ - _ * g p a b + Λ * g p a b) =
    -(1/κ) * (_ - _ * g p b a + Λ * g p b a)
  rw [coordinate_ricci_symmetric_on_regular_lorentz g p domain a b,domain.1 p a b]

end
end AASCSemanticExhaustion
