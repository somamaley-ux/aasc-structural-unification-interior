import C2GeneralPointCurvatureNaturality
import EinsteinOriginalCurvatureResponse

namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Filter
open scoped Topology

theorem coordinate_jacobian_source_translation (F : CoordinatePoint → CoordinatePoint)
    (p x : CoordinatePoint) (regular : DifferentiableAt ℝ F (x+p)) :
    coordinateJacobian (fun y => F (y+p)) x=coordinateJacobian F (x+p) := by
  have hd := regular.hasFDerivAt.comp x (translation_vector_hasFDerivAt p x)
  change HasFDerivAt (fun y => F (y+p))
    ((fderiv ℝ F (x+p)).comp (ContinuousLinearMap.id ℝ CoordinatePoint)) x at hd
  have deriv : fderiv ℝ (fun y => F (y+p)) x=fderiv ℝ F (x+p) := by
    simpa only [ContinuousLinearMap.comp_id] using hd.fderiv
  ext i j
  rw [coordinateJacobian_vector _ x hd.differentiableAt,
    coordinateJacobian_vector F (x+p) regular,deriv]

theorem source_translated_metric_pullback_eventually (g : MetricField)
    (F : CoordinatePoint → CoordinatePoint) (p : CoordinatePoint)
    (regular : ContDiffAt ℝ 3 F p) :
    ∀ᶠ x in 𝓝 0,coordinateMetricPullback g (fun y => F (y+p)) x=
      coordinateMetricPullback g F (x+p) := by
  have near := regular.eventually (by norm_num)
  have shifted : ∀ᶠ x in 𝓝 0, ContDiffAt ℝ 3 F (x+p) := by
    apply (show ContinuousAt (fun x : CoordinatePoint => x+p) 0 from continuousAt_id.add continuousAt_const).tendsto.eventually
    simpa only [zero_add] using near
  filter_upwards [shifted] with x hx
  rw [coordinateMetricPullback_matrix,coordinateMetricPullback_matrix,
    coordinate_jacobian_source_translation F p x (hx.differentiableAt (by norm_num))]

theorem c3_metric_pullback_c2_at (g : MetricField) (F : CoordinatePoint → CoordinatePoint)
    (p : CoordinatePoint) (regularF : ContDiffAt ℝ 3 F p)
    (regularG : ∀ i j,ContDiffAt ℝ 2 (fun x => g x i j) (F p)) (a b : Fin 4) :
    ContDiffAt ℝ 2 (fun x => coordinateMetricPullback g F x a b) p := by
  unfold coordinateMetricPullback
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact ((c3_coordinateJacobian_c2 F p regularF i a).mul
    ((regularG i j).comp p (regularF.of_le (by norm_num)))).mul
      (c3_coordinateJacobian_c2 F p regularF j b)

theorem c2_coordinate_curvature_natural_at_any_point (g : MetricField)
    (symmetric : MetricFieldSymmetric g) (F : CoordinatePoint → CoordinatePoint)
    (p : CoordinatePoint) (regularG : ∀ a b,ContDiffAt ℝ 2 (fun x => g x a b) (F p))
    (nondegenerate : (g (F p)).det≠0) (regularF : ContDiffAt ℝ 3 F p)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (derivative : HasFDerivAt F B.toContinuousLinearMap p) :
    loweredConnectionCurvature (coordinateMetricPullback g F)
        (leviCivitaCoefficients (coordinateMetricPullback g F)) p =
      pullbackFour (coordinateJacobian F p)
        (loweredConnectionCurvature g (leviCivitaCoefficients g) (F p)) := by
  let Ft := fun x : CoordinatePoint => F (x+p)
  have regularFt : ContDiffAt ℝ 3 Ft 0 := by
    have hf : ContDiffAt ℝ 3 F (0+p) := by simpa only [zero_add] using regularF
    apply hf.comp 0
    fun_prop
  have derivativeFt : HasFDerivAt Ft B.toContinuousLinearMap 0 := by
    have hd : HasFDerivAt F B.toContinuousLinearMap (0+p) := by simpa only [zero_add] using derivative
    simpa only [zero_add,ContinuousLinearMap.comp_id] using
      hd.comp 0 (translation_vector_hasFDerivAt p 0)
  have target : Ft 0=F p := by simp [Ft]
  have hnatural := c2_coordinate_leviCivita_curvature_natural_at_target g (F p)
    symmetric regularG nondegenerate Ft regularFt target B derivativeFt
  have regPB := c3_metric_pullback_c2_at g F p regularF regularG
  have ndPB : (coordinateMetricPullback g F p).det≠0 := by
    rw [coordinateMetricPullback_matrix]
    have jac : coordinateJacobian F p=coordinateFrameMatrix B := by
      ext i j
      rw [coordinateJacobian_vector F p derivative.differentiableAt,derivative.fderiv]
      rfl
    rw [jac]
    exact frame_metric_pullback_nondegenerate _ nondegenerate B
  have symPB := coordinateMetricPullback_symmetric g symmetric F
  have regularPBt := c2_metric_translated_regular (coordinateMetricPullback g F) p regPB
  have regularPBft := c3_coordinateMetricPullback_c2 g Ft regularFt
    (by simpa only [target] using regularG)
  have same := metric_twojet_of_eventuallyEq (coordinateMetricPullback g Ft)
    (fun x => coordinateMetricPullback g F (x+p)) 0
      (source_translated_metric_pullback_eventually g F p regularF)
  have ndPBt : ((fun x => coordinateMetricPullback g F (x+p)) 0).det≠0 := by
    simpa only [zero_add] using ndPB
  have ndPBft : (coordinateMetricPullback g Ft 0).det≠0 := by rw [same.1];exact ndPBt
  have curvatureSame := c2_general_curvature_twojet_congr _ _ 0
    (coordinateMetricPullback_symmetric g symmetric Ft) (fun x a b => symPB (x+p) a b)
      regularPBft regularPBt ndPBft ndPBt same
  have translation := c2_coordinate_curvature_translation (coordinateMetricPullback g F) p symPB regPB ndPB
  calc
    _ = loweredConnectionCurvature (coordinateMetricPullback g Ft)
        (leviCivitaCoefficients (coordinateMetricPullback g Ft)) 0 := translation.symm.trans curvatureSame.symm
    _ = _ := by
      rw [hnatural]
      have jac := coordinate_jacobian_source_translation F p 0
        (by simpa only [zero_add] using derivative.differentiableAt)
      simpa only [Ft,zero_add] using congrArg
        (fun J => pullbackFour J (loweredConnectionCurvature g (leviCivitaCoefficients g) (F p))) jac


theorem invertible_frame_inverse_congruence (G : Tensor2) (nondegenerate : G.det≠0)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) :
    ((coordinateFrameMatrix B).transpose * G * coordinateFrameMatrix B)⁻¹ =
      coordinateFrameMatrix B.symm * G⁻¹ * (coordinateFrameMatrix B.symm).transpose := by
  apply Matrix.inv_eq_right_inv
  have ht : (coordinateFrameMatrix B).transpose * (coordinateFrameMatrix B.symm).transpose=1 := by
    rw [← Matrix.transpose_mul,coordinateFrameMatrix_left_inverse,Matrix.transpose_one]
  calc
    _ = (coordinateFrameMatrix B).transpose * G *
        (coordinateFrameMatrix B * coordinateFrameMatrix B.symm) * G⁻¹ *
          (coordinateFrameMatrix B.symm).transpose := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [coordinateFrameMatrix_right_inverse,mul_one,
        Matrix.mul_assoc (coordinateFrameMatrix B).transpose G G⁻¹,
        Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr nondegenerate),mul_one,ht]

theorem inverse_frame_contraction_recovery (G : Tensor2) (nondegenerate : G.det≠0)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) :
    coordinateFrameMatrix B *
      ((coordinateFrameMatrix B).transpose * G * coordinateFrameMatrix B)⁻¹ *
        (coordinateFrameMatrix B).transpose=G⁻¹ := by
  rw [invertible_frame_inverse_congruence G nondegenerate B]
  have ht : (coordinateFrameMatrix B.symm).transpose * (coordinateFrameMatrix B).transpose=1 := by
    rw [← Matrix.transpose_mul,coordinateFrameMatrix_right_inverse,Matrix.transpose_one]
  calc
    _ = (coordinateFrameMatrix B * coordinateFrameMatrix B.symm) * G⁻¹ *
      ((coordinateFrameMatrix B.symm).transpose * (coordinateFrameMatrix B).transpose) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [coordinateFrameMatrix_right_inverse,ht,one_mul,mul_one]

theorem coordinate_ricci_regular_natural (g : MetricField)
    (symmetric : MetricFieldSymmetric g) (F : CoordinatePoint → CoordinatePoint)
    (p : CoordinatePoint) (regularG : ∀ a b,ContDiffAt ℝ 2 (fun x => g x a b) (F p))
    (nondegenerate : (g (F p)).det≠0) (regularF : ContDiffAt ℝ 3 F p)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (derivative : HasFDerivAt F B.toContinuousLinearMap p) :
    coordinateRicci (coordinateMetricPullback g F) p=
      (coordinateJacobian F p).transpose * coordinateRicci g (F p) * coordinateJacobian F p := by
  have jac : coordinateJacobian F p=coordinateFrameMatrix B := by
    ext i j
    rw [coordinateJacobian_vector F p derivative.differentiableAt,derivative.fderiv]
    rfl
  have inv : coordinateJacobian F p * (coordinateMetricPullback g F p)⁻¹ *
      (coordinateJacobian F p).transpose=(g (F p))⁻¹ := by
    rw [coordinateMetricPullback_matrix,jac]
    exact inverse_frame_contraction_recovery _ nondegenerate B
  change tensorRicci (coordinateMetricPullback g F p)⁻¹
      (loweredConnectionCurvature (coordinateMetricPullback g F)
        (leviCivitaCoefficients (coordinateMetricPullback g F)) p)=_
  rw [c2_coordinate_curvature_natural_at_any_point g symmetric F p regularG nondegenerate regularF B derivative]
  exact tensorRicci_pullback _ _ _ _ inv

theorem coordinate_scalar_regular_natural (g : MetricField)
    (symmetric : MetricFieldSymmetric g) (F : CoordinatePoint → CoordinatePoint)
    (p : CoordinatePoint) (regularG : ∀ a b,ContDiffAt ℝ 2 (fun x => g x a b) (F p))
    (nondegenerate : (g (F p)).det≠0) (regularF : ContDiffAt ℝ 3 F p)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (derivative : HasFDerivAt F B.toContinuousLinearMap p) :
    coordinateScalarCurvature (coordinateMetricPullback g F) p=coordinateScalarCurvature g (F p) := by
  change matrixContractionLinear (coordinateMetricPullback g F p)⁻¹
      (coordinateRicci (coordinateMetricPullback g F) p)=_
  rw [coordinate_ricci_regular_natural g symmetric F p regularG nondegenerate regularF B derivative,
    matrixContraction_pullback]
  have jac : coordinateJacobian F p=coordinateFrameMatrix B := by
    ext i j
    rw [coordinateJacobian_vector F p derivative.differentiableAt,derivative.fderiv]
    rfl
  rw [coordinateMetricPullback_matrix,jac,inverse_frame_contraction_recovery _ nondegenerate B]
  rfl

theorem coordinate_ricci_symmetric_on_regular_lorentz (g : MetricField) (p : CoordinatePoint)
    (domain : C2LorentzMetricAt g p) (a b : Fin 4) :
    coordinateRicci g p a b=coordinateRicci g p b a := by
  obtain ⟨B,frame⟩ := domain.2.2
  let R := framedActualConnectionCurvature g p B domain.1 domain.2.1 frame
  have he := framedActualConnectionCurvature_ricci g p B domain.1 domain.2.1 frame
  have hs : ((coordinateFrameMatrix B).transpose * coordinateRicci g p * coordinateFrameMatrix B).transpose=
      (coordinateFrameMatrix B).transpose * coordinateRicci g p * coordinateFrameMatrix B := by
    rw [← he]
    ext i j
    exact ricciResponse_symmetric R j i
  have hsym : (coordinateRicci g p).transpose=coordinateRicci g p := by
    apply frame_matrix_pullback_injective B
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc] using hs
  exact congrArg (fun T : Tensor2 => T b a) hsym

end
end AASCSemanticExhaustion
