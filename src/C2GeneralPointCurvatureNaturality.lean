import C2TranslationMetricJets

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0
set_option autoImplicit false

def targetShiftedCoordinateMap (F : CoordinatePoint → CoordinatePoint) (p : CoordinatePoint) :=
  fun x => F x - p

theorem target_shifted_coordinate_jacobian (F : CoordinatePoint → CoordinatePoint)
    (p x : CoordinatePoint) (regular : DifferentiableAt ℝ F x) :
    coordinateJacobian (targetShiftedCoordinateMap F p) x = coordinateJacobian F x := by
  have hd := regular.hasFDerivAt.sub_const p
  change HasFDerivAt (targetShiftedCoordinateMap F p) (fderiv ℝ F x) x at hd
  ext i a
  rw [coordinateJacobian_vector (targetShiftedCoordinateMap F p) x hd.differentiableAt, hd.fderiv,
    coordinateJacobian_vector F x regular]

theorem target_shifted_metric_pullback_eventually (g : MetricField) (p : CoordinatePoint)
    (F : CoordinatePoint → CoordinatePoint) (regular : ContDiffAt ℝ 3 F 0) :
    ∀ᶠ x in nhds 0,
      coordinateMetricPullback (fun y => g (y + p)) (targetShiftedCoordinateMap F p) x =
        coordinateMetricPullback g F x := by
  have hs := regular.eventually (by norm_num)
  filter_upwards [hs] with x hx
  rw [coordinateMetricPullback_matrix, coordinateMetricPullback_matrix,
    target_shifted_coordinate_jacobian F p x (hx.differentiableAt (by norm_num))]
  simp only [targetShiftedCoordinateMap, sub_add_cancel]

/-- Full actual coordinate curvature transport from a general point of a C²
nondegenerate metric, using a C³ coordinate map with invertible derivative. -/
theorem c2_coordinate_leviCivita_curvature_natural_at_target (g : MetricField) (p : CoordinatePoint)
    (symmetric : MetricFieldSymmetric g) (regularG : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (nondegenerate : (g p).det ≠ 0) (F : CoordinatePoint → CoordinatePoint)
    (regularF : ContDiffAt ℝ 3 F 0) (target : F 0 = p)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (derivative : HasFDerivAt F B.toContinuousLinearMap 0) :
    loweredConnectionCurvature (coordinateMetricPullback g F) (leviCivitaCoefficients (coordinateMetricPullback g F)) 0 =
      pullbackFour (coordinateJacobian F 0) (loweredConnectionCurvature g (leviCivitaCoefficients g) p) := by
  let gt := fun x => g (x + p)
  let Ft := targetShiftedCoordinateMap F p
  have symGT : MetricFieldSymmetric gt := fun x a b => symmetric (x + p) a b
  have regGT := c2_metric_translated_regular g p regularG
  have ndGT : (gt 0).det ≠ 0 := by simpa only [gt, zero_add] using nondegenerate
  have regFT : ContDiffAt ℝ 3 Ft 0 := regularF.sub contDiffAt_const
  have zeroFT : Ft 0 = 0 := by simp [Ft, targetShiftedCoordinateMap, target]
  have derivativeFT : HasFDerivAt Ft B.toContinuousLinearMap 0 := derivative.sub_const p
  have regPB : ∀ a b, ContDiffAt ℝ 2 (fun x => coordinateMetricPullback g F x a b) 0 :=
    c3_coordinateMetricPullback_c2 g F regularF (by simpa only [target] using regularG)
  have regPBT := c3_coordinateMetricPullback_c2 gt Ft regFT (by simpa only [zeroFT] using regGT)
  have ndPB : (coordinateMetricPullback g F 0).det ≠ 0 := by
    rw [coordinateMetricPullback_matrix, target, coordinateJacobian_of_derivative_equiv F B derivative]
    exact frame_metric_pullback_nondegenerate (g p) nondegenerate B
  have equal := metric_twojet_of_eventuallyEq (coordinateMetricPullback gt Ft)
    (coordinateMetricPullback g F) 0 (target_shifted_metric_pullback_eventually g p F regularF)
  have ndPBT : (coordinateMetricPullback gt Ft 0).det ≠ 0 := by rw [equal.1]; exact ndPB
  have heq := c2_general_curvature_twojet_congr (coordinateMetricPullback gt Ft) (coordinateMetricPullback g F) 0
    (coordinateMetricPullback_symmetric gt symGT Ft) (coordinateMetricPullback_symmetric g symmetric F)
      regPBT regPB ndPBT ndPB equal
  have hn := c2_coordinate_leviCivita_curvature_natural_zero gt symGT regGT ndGT Ft regFT zeroFT B derivativeFT
  calc
    loweredConnectionCurvature (coordinateMetricPullback g F) (leviCivitaCoefficients (coordinateMetricPullback g F)) 0 =
        loweredConnectionCurvature (coordinateMetricPullback gt Ft) (leviCivitaCoefficients (coordinateMetricPullback gt Ft)) 0 := heq.symm
    _ = pullbackFour (coordinateJacobian Ft 0) (loweredConnectionCurvature gt (leviCivitaCoefficients gt) 0) := hn
    _ = pullbackFour (coordinateJacobian F 0) (loweredConnectionCurvature g (leviCivitaCoefficients g) p) := by
      rw [c2_coordinate_curvature_translation g p symmetric regularG nondegenerate,
        target_shifted_coordinate_jacobian F p 0 derivative.differentiableAt]

#print axioms target_shifted_coordinate_jacobian
#print axioms target_shifted_metric_pullback_eventually
#print axioms c2_coordinate_leviCivita_curvature_natural_at_target
end
end AASCSemanticExhaustion
