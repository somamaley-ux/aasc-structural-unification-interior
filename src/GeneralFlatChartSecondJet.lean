import GeneralMetricNormalizingCurvature

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0
set_option autoImplicit false

theorem frame_metric_lowering_left_inverse (G : Tensor2) (nondegenerate : G.det ≠ 0)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) :
    (G⁻¹ * (coordinateFrameMatrix B.symm).transpose) * ((coordinateFrameMatrix B).transpose * G) = 1 := by
  calc
    _ = G⁻¹ * (((coordinateFrameMatrix B.symm).transpose * (coordinateFrameMatrix B).transpose) * G) := by
      simp only [Matrix.mul_assoc]
    _ = G⁻¹ * (((coordinateFrameMatrix B * coordinateFrameMatrix B.symm).transpose) * G) := by
      rw [Matrix.transpose_mul]
    _ = 1 := by
      rw [coordinateFrameMatrix_right_inverse, Matrix.transpose_one, one_mul]
      exact Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.mpr nondegenerate)

theorem frame_metric_lowering_injective (G : Tensor2) (nondegenerate : G.det ≠ 0)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (q : CoordinatePoint)
    (zero : ∀ a, (∑ i : Fin 4, ∑ j : Fin 4, coordinateFrameMatrix B i a * G i j * q j) = 0) : q = 0 := by
  have hz : ((coordinateFrameMatrix B).transpose * G).mulVec q = 0 := by
    ext a
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact zero a
  have h := congrArg (fun v => (G⁻¹ * (coordinateFrameMatrix B.symm).transpose).mulVec v) hz
  dsimp only at h
  rw [Matrix.mulVec_mulVec, frame_metric_lowering_left_inverse G nondegenerate B] at h
  simpa only [Matrix.one_mulVec, Matrix.mulVec_zero] using h

theorem first_flat_metric_general_chart_partial (g : MetricField)
    (regularG : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) 0)
    (firstG : ∀ a b, fderiv ℝ (fun x => g x a b) 0 = 0)
    (F : CoordinatePoint → CoordinatePoint) (regularF : ContDiffAt ℝ 3 F 0) (zeroF : F 0 = 0)
    (a b c : Fin 4) :
    scalarPartial (fun x => coordinateMetricPullback g F x a b) 0 c =
      (∑ i : Fin 4, ∑ j : Fin 4,
        (coordinateJacobian F 0 i a * g 0 i j * scalarPartial (fun x => coordinateJacobian F x j b) 0 c +
        coordinateJacobian F 0 j b * g 0 i j * scalarPartial (fun x => coordinateJacobian F x i a) 0 c)) := by
  have hj (i k : Fin 4) := ((c3_coordinateJacobian_c2 F 0 regularF i k).differentiableAt
    (by norm_num)).hasFDerivAt
  have hb (i j : Fin 4) : HasFDerivAt (𝕜 := ℝ) (fun x => g (F x) i j) 0 0 := by
    have hs : ContDiffAt ℝ 2 (fun x => g x i j) (F 0) := by simpa only [zeroF] using regularG i j
    have hd := ((hs.comp 0 (regularF.of_le (by norm_num))).differentiableAt (by norm_num)).hasFDerivAt
    have hz := c2_local_scalarFirstJet_comp_zero (fun x => g x i j) F (regularG i j)
      (regularF.of_le (by norm_num)) zeroF (firstG i j)
    change HasFDerivAt (fun x => g (F x) i j) (fderiv ℝ (fun x => g (F x) i j) 0) 0 at hd
    rw [hz] at hd
    exact hd
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => ((hj i a).mul (hb i j)).mul (hj j b)))
  have hd := hs.fderiv
  change fderiv ℝ (fun x => coordinateMetricPullback g F x a b) 0 = _ at hd
  unfold scalarPartial
  rw [hd]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply, smul_eq_mul,
    Pi.mul_apply, zeroF, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem first_flat_metrics_force_chart_second_zero (g : MetricField)
    (symmetric : MetricFieldSymmetric g) (regularG : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) 0)
    (nondegenerate : (g 0).det ≠ 0) (firstG : ∀ a b, fderiv ℝ (fun x => g x a b) 0 = 0)
    (F : CoordinatePoint → CoordinatePoint) (regularF : ContDiffAt ℝ 3 F 0) (zeroF : F 0 = 0)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (frame : coordinateJacobian F 0 = coordinateFrameMatrix B)
    (normal : ∀ a b, fderiv ℝ (fun x => coordinateMetricPullback g F x a b) 0 = 0) :
    ∀ i a, fderiv ℝ (fun x => coordinateJacobian F x i a) 0 = 0 := by
  let Q := fun i a c => scalarPartial (fun x => coordinateJacobian F x i a) 0 c
  let T := fun a b c => ∑ i : Fin 4, ∑ j : Fin 4, coordinateFrameMatrix B i a * g 0 i j * Q j b c
  have qs (i a c : Fin 4) : Q i a c = Q i c a := coordinate_second_partial_symmetric F regularF i a c
  have ts (a b c : Fin 4) : T a b c = T a c b := by
    dsimp only [T]
    simp_rw [qs _ b c]
  have anti (a b c : Fin 4) : T a b c + T b a c = 0 := by
    have h := first_flat_metric_general_chart_partial g regularG firstG F regularF zeroF a b c
    rw [frame] at h
    have hz : scalarPartial (fun x => coordinateMetricPullback g F x a b) 0 c = 0 := by
      simp [scalarPartial, normal]
    have hs : (∑ i : Fin 4, ∑ j : Fin 4,
        coordinateFrameMatrix B j b * g 0 i j * Q i a c) = T b a c := by
      dsimp only [T]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [symmetric 0 j i]
    simp only [Finset.sum_add_distrib] at h
    change _ = T a b c + _ at h
    rw [hs] at h
    exact h.symm.trans hz
  have tz (a b c : Fin 4) : T a b c = 0 := by
    have h1 := anti a b c
    have h2 := anti a c b
    have h3 := anti b c a
    rw [ts b a c] at h1
    rw [ts c a b, ts a c b] at h2
    linarith
  intro i a
  apply continuousLinearMap_zero_of_coordinate_basis
  intro c
  have hz := frame_metric_lowering_injective (g 0) nondegenerate B (fun j => Q j a c)
    (fun b => tz b a c)
  exact congrArg (fun q : CoordinatePoint => q i) hz

#print axioms frame_metric_lowering_left_inverse
#print axioms frame_metric_lowering_injective
#print axioms first_flat_metric_general_chart_partial
#print axioms first_flat_metrics_force_chart_second_zero
end
end AASCSemanticExhaustion
