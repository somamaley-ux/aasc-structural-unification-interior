import GeneralFlatChartSecondJet

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0
set_option autoImplicit false

def frameLoweredThirdJet (A G : Tensor2) (C : Tensor4) : Tensor4 := fun a b c d =>
  ∑ i : Fin 4, ∑ j : Fin 4, A i a * G i j * C j b c d

theorem frameLoweredThirdJet_cubic (A G : Tensor2) (C : Tensor4) (laws : CubicCoordinateLaws C) :
    CubicCoordinateLaws (frameLoweredThirdJet A G C) := by
  constructor
  · intro a b c d
    unfold frameLoweredThirdJet
    simp_rw [laws.1 _ b c d]
  · intro a b c d
    unfold frameLoweredThirdJet
    simp_rw [laws.2 _ b c d]

theorem curvatureOfSymmetricCubicGauge_zero (T : Tensor4) (laws : CubicCoordinateLaws T) :
    curvatureOfNormalHessian (fun a b c d => T a b c d + T b a c d) = 0 := by
  funext a b c d
  change curvatureOfNormalHessian (fun a b c d => T a b c d + T b a c d) a b c d = 0
  unfold curvatureOfNormalHessian
  linarith [laws.1 a d b c, laws.2 a b d c, laws.1 a b c d, laws.1 d a b c,
    laws.1 b c a d, laws.2 b a c d, laws.1 b a d c, laws.1 c b a d]

theorem c2_first_flat_scalar_composition_second (f : CoordinatePoint → ℝ)
    (regular : ContDiffAt ℝ 2 f 0) (first : fderiv ℝ f 0 = 0)
    (F : CoordinatePoint → CoordinatePoint) (regularF : ContDiffAt ℝ 3 F 0) (zeroF : F 0 = 0)
    (c d : Fin 4) :
    scalarSecondPartial (fun x => f (F x)) 0 c d =
      ∑ u : Fin 4, ∑ v : Fin 4, scalarSecondPartial f 0 u v * coordinateJacobian F 0 u c * coordinateJacobian F 0 v d := by
  have hf : ContDiffAt ℝ 2 f (F 0) := by simpa only [zeroF] using regular
  rw [c2_local_scalarSecondPartial_comp f F 0 hf (regularF.of_le (by norm_num)), zeroF, first]
  simp only [ContinuousLinearMap.zero_apply, zero_add]
  rw [continuousBilinear_four_coordinates, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [c2_scalarSecondPartial_full_second_derivative f 0 regular u v]
  rw [coordinateJacobian_vector F 0 (regularF.differentiableAt (by norm_num)),
    coordinateJacobian_vector F 0 (regularF.differentiableAt (by norm_num))]
  ring

theorem c2_first_flat_metric_pullback_hessian (g : MetricField)
    (symmetric : MetricFieldSymmetric g) (regularG : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) 0)
    (firstG : ∀ a b, fderiv ℝ (fun x => g x a b) 0 = 0)
    (F : CoordinatePoint → CoordinatePoint) (regularF : ContDiffAt ℝ 3 F 0) (zeroF : F 0 = 0)
    (secondF : ∀ i a, fderiv ℝ (fun x => coordinateJacobian F x i a) 0 = 0) :
    ((c2MetricHessian (coordinateMetricPullback g F) 0 (coordinateMetricPullback_symmetric g symmetric F)
      (c3_coordinateMetricPullback_c2 g F regularF (by simpa only [zeroF] using regularG)) : metricHessianSpace) : Tensor4) =
      pullbackFour (coordinateJacobian F 0) (c2MetricHessian g 0 symmetric regularG) +
        (fun a b c d => frameLoweredThirdJet (coordinateJacobian F 0) (g 0) (coordinateThirdJet F 0) a b c d +
          frameLoweredThirdJet (coordinateJacobian F 0) (g 0) (coordinateThirdJet F 0) b a c d) := by
  funext a b c d
  let J := fun i k x => coordinateJacobian F x i k
  let B := fun i j x => g (F x) i j
  let W := fun i j x => J i a x * B i j x * J j b x
  have hj (i k : Fin 4) : ContDiffAt ℝ 2 (J i k) 0 := c3_coordinateJacobian_c2 F 0 regularF i k
  have hb (i j : Fin 4) : ContDiffAt ℝ 2 (B i j) 0 := by
    have hs : ContDiffAt ℝ 2 (fun x => g x i j) (F 0) := by simpa only [zeroF] using regularG i j
    exact hs.comp 0 (regularF.of_le (by norm_num))
  have hw (i j : Fin 4) : ContDiffAt ℝ 2 (W i j) 0 := ((hj i a).mul (hb i j)).mul (hj j b)
  have hb1 (i j : Fin 4) : fderiv ℝ (B i j) 0 = 0 :=
    c2_local_scalarFirstJet_comp_zero _ F (regularG i j) (regularF.of_le (by norm_num)) zeroF (firstG i j)
  have hb0 (i j : Fin 4) : B i j 0 = g 0 i j := by simp [B, zeroF]
  have hb2 (i j : Fin 4) : scalarSecondPartial (B i j) 0 c d =
      ∑ u : Fin 4, ∑ v : Fin 4, scalarSecondPartial (fun x => g x i j) 0 u v *
        coordinateJacobian F 0 u c * coordinateJacobian F 0 v d :=
    c2_first_flat_scalar_composition_second _ (regularG i j) (firstG i j) F regularF zeroF c d
  have hW (i j : Fin 4) := c2_local_scalarSecondPartial_triple_flat (J i a) (B i j) (J j b)
    (hj i a) (hb i j) (hj j b) (secondF i a) (hb1 i j) (secondF j b) c d
  simp only [hb0, hb2] at hW
  have ho (i : Fin 4) : ContDiffAt ℝ 2 (fun x => ∑ j, W i j x) 0 := ContDiffAt.sum (fun j _ => hw i j)
  change scalarSecondPartial (fun x => ∑ i : Fin 4, ∑ j : Fin 4, W i j x) 0 c d = _
  rw [c2_local_scalarSecondPartial_sum _ 0 ho c d]
  simp_rw [c2_local_scalarSecondPartial_sum _ 0 (hw _) c d]
  dsimp only [W]
  simp_rw [hW]
  have hm : (∑ i : Fin 4, ∑ j : Fin 4, J i a 0 * J j b 0 *
      (∑ u : Fin 4, ∑ v : Fin 4, scalarSecondPartial (fun x => g x i j) 0 u v *
        coordinateJacobian F 0 u c * coordinateJacobian F 0 v d)) =
      pullbackFour (coordinateJacobian F 0) (c2MetricHessian g 0 symmetric regularG) a b c d := by
    rw [pullbackFour_flat]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    change _ = _ * scalarSecondPartial (fun x => g x i j) 0 u v
    ring
  have hr : (∑ i : Fin 4, ∑ j : Fin 4, g 0 i j * J j b 0 * scalarSecondPartial (J i a) 0 c d) =
      frameLoweredThirdJet (coordinateJacobian F 0) (g 0) (coordinateThirdJet F 0) b a c d := by
    unfold frameLoweredThirdJet
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [symmetric 0 j i]
    change _ = coordinateJacobian F 0 i b * g 0 i j * scalarSecondPartial (J j a) 0 c d
    ring
  simp only [Finset.sum_add_distrib]
  rw [hm, hr]
  change frameLoweredThirdJet (coordinateJacobian F 0) (g 0) (coordinateThirdJet F 0) a b c d +
    pullbackFour (coordinateJacobian F 0) (c2MetricHessian g 0 symmetric regularG) a b c d +
      frameLoweredThirdJet (coordinateJacobian F 0) (g 0) (coordinateThirdJet F 0) b a c d =
    pullbackFour (coordinateJacobian F 0) (c2MetricHessian g 0 symmetric regularG) a b c d +
      (frameLoweredThirdJet (coordinateJacobian F 0) (g 0) (coordinateThirdJet F 0) a b c d +
        frameLoweredThirdJet (coordinateJacobian F 0) (g 0) (coordinateThirdJet F 0) b a c d)
  ring

theorem c2_first_flat_general_chart_curvature_transport (g : MetricField)
    (symmetric : MetricFieldSymmetric g) (regularG : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) 0)
    (nondegenerate : (g 0).det ≠ 0) (firstG : ∀ a b, fderiv ℝ (fun x => g x a b) 0 = 0)
    (F : CoordinatePoint → CoordinatePoint) (regularF : ContDiffAt ℝ 3 F 0) (zeroF : F 0 = 0)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (frame : coordinateJacobian F 0 = coordinateFrameMatrix B)
    (nondegenerateF : (coordinateMetricPullback g F 0).det ≠ 0)
    (normal : ∀ a b, fderiv ℝ (fun x => coordinateMetricPullback g F x a b) 0 = 0) :
    loweredConnectionCurvature (coordinateMetricPullback g F) (leviCivitaCoefficients (coordinateMetricPullback g F)) 0 =
      pullbackFour (coordinateJacobian F 0) (loweredConnectionCurvature g (leviCivitaCoefficients g) 0) := by
  have regF := c3_coordinateMetricPullback_c2 g F regularF (by simpa only [zeroF] using regularG)
  have zero2 := first_flat_metrics_force_chart_second_zero g symmetric regularG nondegenerate firstG F regularF zeroF B frame normal
  have hc : loweredConnectionCurvature (coordinateMetricPullback g F)
      (leviCivitaCoefficients (coordinateMetricPullback g F)) 0 =
        curvatureOfNormalHessian (c2MetricHessian (coordinateMetricPullback g F) 0
          (coordinateMetricPullback_symmetric g symmetric F) regF) := by
    funext a b c d
    exact c2_first_flat_metric_curvature _ _ regF nondegenerateF normal a b c d
  have hg : loweredConnectionCurvature g (leviCivitaCoefficients g) 0 =
      curvatureOfNormalHessian (c2MetricHessian g 0 symmetric regularG) := by
    funext a b c d
    exact c2_first_flat_metric_curvature g symmetric regularG nondegenerate firstG a b c d
  rw [hc, c2_first_flat_metric_pullback_hessian g symmetric regularG firstG F regularF zeroF zero2,
    curvatureOfNormalHessian_add, curvatureOfNormalHessian_pullback,
    curvatureOfSymmetricCubicGauge_zero _ (frameLoweredThirdJet_cubic _ _ _
      (coordinateThirdJet_cubic_laws F 0 regularF)), add_zero, hg]

#print axioms frameLoweredThirdJet_cubic
#print axioms curvatureOfSymmetricCubicGauge_zero
#print axioms c2_first_flat_scalar_composition_second
#print axioms c2_first_flat_metric_pullback_hessian
#print axioms c2_first_flat_general_chart_curvature_transport
end
end AASCSemanticExhaustion
