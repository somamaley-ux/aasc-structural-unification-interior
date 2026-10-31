import ThirdCoordinateJet
import C2LocalSecondJetComposition

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

/-- An independent condition on the actual first two coordinate jets. -/
def IdentityCoordinateSecondJet (F : CoordinatePoint → CoordinatePoint) : Prop :=
  F 0 = 0 ∧ fderiv ℝ F 0 = ContinuousLinearMap.id ℝ CoordinatePoint ∧
    ∀ i a, fderiv ℝ (fun x => coordinateJacobian F x i a) 0 = 0

theorem identity_second_jet_jacobian (F : CoordinatePoint → CoordinatePoint)
    (regular : ContDiffAt ℝ 3 F 0) (jet : IdentityCoordinateSecondJet F) :
    coordinateJacobian F 0 = 1 := by
  ext i a
  rw [coordinateJacobian_vector F 0 (regular.differentiableAt (by norm_num)), jet.2.1]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

theorem identity_second_jet_actual_local_chart (F : CoordinatePoint → CoordinatePoint)
    (regular : ContDiffAt ℝ 3 F 0) (jet : IdentityCoordinateSecondJet F) :
    ∃ e : OpenPartialHomeomorph CoordinatePoint CoordinatePoint,
      0 ∈ e.source ∧ (e : CoordinatePoint → CoordinatePoint) = F := by
  have hd : HasFDerivAt F (ContinuousLinearEquiv.refl ℝ CoordinatePoint).toContinuousLinearMap 0 := by
    simpa only [jet.2.1] using (regular.differentiableAt (by norm_num)).hasFDerivAt
  refine ⟨regular.toOpenPartialHomeomorph F hd (by norm_num), ?_, rfl⟩
  exact regular.mem_toOpenPartialHomeomorph_source hd (by norm_num)

theorem c3_coordinateMetricPullback_c2 (g : MetricField) (F : CoordinatePoint → CoordinatePoint)
    (regularF : ContDiffAt ℝ 3 F 0)
    (regularG : ∀ i j, ContDiffAt ℝ 2 (fun x => g x i j) (F 0)) (a b : Fin 4) :
    ContDiffAt ℝ 2 (fun x => coordinateMetricPullback g F x a b) 0 := by
  unfold coordinateMetricPullback
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact ((c3_coordinateJacobian_c2 F 0 regularF i a).mul
    ((regularG i j).comp 0 (regularF.of_le (by norm_num)))).mul
      (c3_coordinateJacobian_c2 F 0 regularF j b)

theorem identity_second_jet_metric_pullback_first (g : MetricField)
    (germ : C2NormalizedMetricGerm g) (F : CoordinatePoint → CoordinatePoint)
    (regular : ContDiffAt ℝ 3 F 0) (jet : IdentityCoordinateSecondJet F) (a b : Fin 4) :
    fderiv ℝ (fun x => coordinateMetricPullback g F x a b) 0 = 0 := by
  have hj (i k : Fin 4) : HasFDerivAt (𝕜 := ℝ)
      (fun x => coordinateJacobian F x i k) 0 0 := by
    have hd := ((c3_coordinateJacobian_c2 F 0 regular i k).differentiableAt
      (by norm_num)).hasFDerivAt
    rw [jet.2.2] at hd
    exact hd
  have hb (i j : Fin 4) : HasFDerivAt (𝕜 := ℝ) (fun x => g (F x) i j) 0 0 := by
    have hs : ContDiffAt ℝ 2 (fun x => g x i j) (F 0) := by
      simpa only [jet.1] using germ.2.1 i j
    have hh := ((hs.comp 0 (regular.of_le (by norm_num))).differentiableAt (by norm_num)).hasFDerivAt
    have hz := c2_local_scalarFirstJet_comp_zero (fun x => g x i j) F (germ.2.1 i j)
      (regular.of_le (by norm_num)) jet.1 (germ.2.2.2 i j)
    change HasFDerivAt (fun x => g (F x) i j) (fderiv ℝ (fun x => g (F x) i j) 0) 0 at hh
    rw [hz] at hh
    exact hh
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => ((hj i a).mul (hb i j)).mul (hj j b)))
  have hd : HasFDerivAt (𝕜 := ℝ) (fun x => coordinateMetricPullback g F x a b) 0 0 := by
    simpa only [coordinateMetricPullback, Pi.mul_apply, zero_smul, smul_zero,
      add_zero, Finset.sum_const_zero] using hs
  exact hd.fderiv

theorem identity_second_jet_metric_pullback_germ (g : MetricField)
    (germ : C2NormalizedMetricGerm g) (F : CoordinatePoint → CoordinatePoint)
    (regular : ContDiffAt ℝ 3 F 0) (jet : IdentityCoordinateSecondJet F) :
    C2NormalizedMetricGerm (coordinateMetricPullback g F) := by
  refine ⟨coordinateMetricPullback_symmetric g germ.1 _, ?_, ?_,
    identity_second_jet_metric_pullback_first g germ F regular jet⟩
  · apply c3_coordinateMetricPullback_c2 g F regular
    simpa only [jet.1] using germ.2.1
  · rw [coordinateMetricPullback_matrix, identity_second_jet_jacobian F regular jet,
      jet.1, Matrix.transpose_one, one_mul, mul_one, germ.2.2.1]

theorem identity_second_jet_metric_pullback_second (g : MetricField)
    (germ : C2NormalizedMetricGerm g) (F : CoordinatePoint → CoordinatePoint)
    (regular : ContDiffAt ℝ 3 F 0) (jet : IdentityCoordinateSecondJet F) (a b c d : Fin 4) :
    scalarSecondPartial (fun x => coordinateMetricPullback g F x a b) 0 c d =
      scalarSecondPartial (fun x => g x a b) 0 c d +
        (∑ i : Fin 4, metric a i * coordinateThirdJet F 0 i b c d) +
          (∑ i : Fin 4, metric i b * coordinateThirdJet F 0 i a c d) := by
  let J := fun i k x => coordinateJacobian F x i k
  let B := fun i j x => g (F x) i j
  let W := fun i j x => J i a x * B i j x * J j b x
  have hj (i k : Fin 4) : ContDiffAt ℝ 2 (J i k) 0 := c3_coordinateJacobian_c2 F 0 regular i k
  have hb (i j : Fin 4) : ContDiffAt ℝ 2 (B i j) 0 := by
    have hs : ContDiffAt ℝ 2 (fun x => g x i j) (F 0) := by
      simpa only [jet.1] using germ.2.1 i j
    exact hs.comp 0 (regular.of_le (by norm_num))
  have hw (i j : Fin 4) : ContDiffAt ℝ 2 (W i j) 0 := ((hj i a).mul (hb i j)).mul (hj j b)
  have hfirstB (i j : Fin 4) : fderiv ℝ (B i j) 0 = 0 :=
    c2_local_scalarFirstJet_comp_zero (fun x => g x i j) F (germ.2.1 i j)
      (regular.of_le (by norm_num)) jet.1 (germ.2.2.2 i j)
  have hvalJ (i k : Fin 4) : J i k 0 = (1 : Tensor2) i k :=
    congrArg (fun M : Tensor2 => M i k) (identity_second_jet_jacobian F regular jet)
  have hvalB (i j : Fin 4) : B i j 0 = metric i j := by
    dsimp [B]
    rw [jet.1, germ.2.2.1]
  have hsecondB (i j : Fin 4) : scalarSecondPartial (B i j) 0 c d =
      scalarSecondPartial (fun x => g x i j) 0 c d :=
    c2_local_scalarSecondPartial_comp_flat_identity (fun x => g x i j) F (germ.2.1 i j)
      (regular.of_le (by norm_num)) jet.1 jet.2.1 (germ.2.2.2 i j) c d
  have hsecondW (i j : Fin 4) : scalarSecondPartial (W i j) 0 c d =
      (1 : Tensor2) i a * metric i j * coordinateThirdJet F 0 j b c d +
        (1 : Tensor2) i a * (1 : Tensor2) j b * scalarSecondPartial (fun x => g x i j) 0 c d +
          metric i j * (1 : Tensor2) j b * coordinateThirdJet F 0 i a c d := by
    rw [c2_local_scalarSecondPartial_triple_flat (J i a) (B i j) (J j b)
      (hj i a) (hb i j) (hj j b) (jet.2.2 i a) (hfirstB i j) (jet.2.2 j b) c d]
    rw [hvalJ, hvalJ, hvalB, hsecondB]
    rfl
  have houter (i : Fin 4) : ContDiffAt ℝ 2 (fun x => ∑ j, W i j x) 0 :=
    ContDiffAt.sum (fun j _ => hw i j)
  change scalarSecondPartial (fun x => ∑ i : Fin 4, ∑ j : Fin 4, W i j x) 0 c d = _
  rw [c2_local_scalarSecondPartial_sum _ 0 houter c d]
  simp_rw [c2_local_scalarSecondPartial_sum _ 0 (hw _) c d, hsecondW]
  simp [Matrix.one_apply, ite_mul, mul_ite, Finset.sum_add_distrib]
  ring

theorem identity_second_jet_metric_hessian_gauge (g : MetricField)
    (germ : C2NormalizedMetricGerm g) (F : CoordinatePoint → CoordinatePoint)
    (regular : ContDiffAt ℝ 3 F 0) (jet : IdentityCoordinateSecondJet F) :
    HasCubicCoordinateGauge
      (c2MetricHessian (coordinateMetricPullback g F) 0
        (identity_second_jet_metric_pullback_germ g germ F regular jet).1
        (identity_second_jet_metric_pullback_germ g germ F regular jet).2.1 -
      c2MetricHessian g 0 germ.1 germ.2.1) := by
  refine ⟨loweredCubicCoordinate (coordinateThirdJet F 0),
    loweredCubicCoordinate_laws _ (coordinateThirdJet_cubic_laws F 0 regular), ?_⟩
  intro a b c d
  change scalarSecondPartial (fun x => coordinateMetricPullback g F x a b) 0 c d -
    scalarSecondPartial (fun x => g x a b) 0 c d = _
  rw [identity_second_jet_metric_pullback_second g germ F regular jet]
  have hs (i : Fin 4) : metric i b = metric b i := by
    by_cases h : i = b
    · subst b; rfl
    · simp [metric, h, Ne.symm h]
  simp_rw [hs]
  unfold loweredCubicCoordinate
  ring

/-- Actual connection curvature, for arbitrary C² metric germs and arbitrary
C³ coordinate germs with the stated identity second jet. -/
theorem c2_leviCivita_identity_second_jet_transport (g : MetricField)
    (germ : C2NormalizedMetricGerm g) (F : CoordinatePoint → CoordinatePoint)
    (regular : ContDiffAt ℝ 3 F 0) (jet : IdentityCoordinateSecondJet F) :
    loweredConnectionCurvature (coordinateMetricPullback g F)
      (leviCivitaCoefficients (coordinateMetricPullback g F)) 0 =
        loweredConnectionCurvature g (leviCivitaCoefficients g) 0 := by
  let germ' := identity_second_jet_metric_pullback_germ g germ F regular jet
  let H := c2MetricHessian g 0 germ.1 germ.2.1
  let K := c2MetricHessian (coordinateMetricPullback g F) 0 germ'.1 germ'.2.1
  have hf : curvatureJetMap (K - H) = 0 :=
    cubic_coordinate_gauge_flat _ (identity_second_jet_metric_hessian_gauge g germ F regular jet)
  have heq : curvatureJetMap K = curvatureJetMap H :=
    sub_eq_zero.mp (by simpa only [map_sub] using hf)
  rw [c2_normalized_metric_leviCivita_curvature _ germ', c2_normalized_metric_leviCivita_curvature g germ]
  exact congrArg (fun R : curvatureSpace => (R : Tensor4)) heq

#print axioms identity_second_jet_jacobian
#print axioms identity_second_jet_actual_local_chart
#print axioms c3_coordinateMetricPullback_c2
#print axioms identity_second_jet_metric_pullback_first
#print axioms identity_second_jet_metric_pullback_germ
#print axioms identity_second_jet_metric_pullback_second
#print axioms identity_second_jet_metric_hessian_gauge
#print axioms c2_leviCivita_identity_second_jet_transport
end
end AASCSemanticExhaustion
