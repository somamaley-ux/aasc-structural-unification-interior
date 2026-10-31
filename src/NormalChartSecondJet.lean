import GeneralNormalizedChartTransport

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

theorem coordinate_second_partial_symmetric (F : CoordinatePoint → CoordinatePoint)
    (regular : ContDiffAt ℝ 3 F 0) (i a c : Fin 4) :
    scalarPartial (fun x => coordinateJacobian F x i a) 0 c =
      scalarPartial (fun x => coordinateJacobian F x i c) 0 a := by
  have hi : ContDiffAt ℝ 2 (fun x => F x i) 0 :=
    (coordinateProjection i).contDiff.contDiffAt.comp 0 (regular.of_le (by norm_num))
  exact c2_scalarSecondPartial_symmetric _ 0 hi a c

theorem general_identity_first_jet_metric_partial (g : MetricField)
    (germ : C2NormalizedMetricGerm g) (F : CoordinatePoint → CoordinatePoint)
    (regular : ContDiffAt ℝ 3 F 0) (Fzero : F 0 = 0)
    (DFzero : fderiv ℝ F 0 = ContinuousLinearMap.id ℝ CoordinatePoint) (a b c : Fin 4) :
    scalarPartial (fun x => coordinateMetricPullback g F x a b) 0 c =
      (∑ i : Fin 4, metric i b * scalarPartial (fun x => coordinateJacobian F x i a) 0 c) +
        (∑ j : Fin 4, metric a j * scalarPartial (fun x => coordinateJacobian F x j b) 0 c) := by
  have hF : HasFDerivAt F (ContinuousLinearMap.id ℝ CoordinatePoint) 0 := by
    simpa only [DFzero] using (regular.differentiableAt (by norm_num)).hasFDerivAt
  have hj0 : coordinateJacobian F 0 = 1 := by
    ext i k
    rw [coordinateJacobian_vector F 0 (regular.differentiableAt (by norm_num)), DFzero]
    simp [Matrix.one_apply, Pi.single_apply]
  have hj (i k : Fin 4) := ((c3_coordinateJacobian_c2 F 0 regular i k).differentiableAt
    (by norm_num)).hasFDerivAt
  have hb (i j : Fin 4) : HasFDerivAt (𝕜 := ℝ) (fun x => g (F x) i j) 0 0 := by
    have hs : DifferentiableAt ℝ (fun x => g x i j) (F 0) := by
      simpa only [Fzero] using (germ.2.1 i j).differentiableAt (by norm_num)
    have hd := hs.hasFDerivAt.comp 0 hF
    change HasFDerivAt (fun x => g (F x) i j)
      ((fderiv ℝ (fun x => g x i j) (F 0)).comp (ContinuousLinearMap.id ℝ CoordinatePoint)) 0 at hd
    simpa only [Fzero, germ.2.2.2, ContinuousLinearMap.zero_comp] using hd
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => ((hj i a).mul (hb i j)).mul (hj j b)))
  have hd := hs.fderiv
  change fderiv ℝ (fun x => coordinateMetricPullback g F x a b) 0 = _ at hd
  unfold scalarPartial
  rw [hd]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply, smul_eq_mul,
    Pi.mul_apply, Fzero, germ.2.2.1, hj0, mul_zero, add_zero]
  simp [Matrix.one_apply, ite_mul, mul_ite, Finset.sum_add_distrib] <;> ring

/-- Normality of both metric germs forces the second coordinate jet to vanish
once their first coordinate frame agrees. This is derived, not a gauge premise. -/
theorem normal_metric_identity_frame_forces_second_jet (g : MetricField)
    (germ : C2NormalizedMetricGerm g) (F : CoordinatePoint → CoordinatePoint)
    (regular : ContDiffAt ℝ 3 F 0) (Fzero : F 0 = 0)
    (DFzero : fderiv ℝ F 0 = ContinuousLinearMap.id ℝ CoordinatePoint)
    (normal : ∀ a b, fderiv ℝ (fun x => coordinateMetricPullback g F x a b) 0 = 0) :
    IdentityCoordinateSecondJet F := by
  let Q := fun i a c => scalarPartial (fun x => coordinateJacobian F x i a) 0 c
  let T := fun a b c => ∑ i : Fin 4, metric a i * Q i b c
  have qs (i a c : Fin 4) : Q i a c = Q i c a := coordinate_second_partial_symmetric F regular i a c
  have ts (a b c : Fin 4) : T a b c = T a c b := by
    dsimp only [T]
    simp_rw [qs _ b c]
  have anti (a b c : Fin 4) : T b a c + T a b c = 0 := by
    have h := general_identity_first_jet_metric_partial g germ F regular Fzero DFzero a b c
    have hm (i : Fin 4) : metric i b = metric b i := by
      by_cases h : i = b
      · subst b; rfl
      · simp [metric, h, Ne.symm h]
    simp_rw [hm] at h
    have hz : scalarPartial (fun x => coordinateMetricPullback g F x a b) 0 c = 0 := by
      simp [scalarPartial, normal]
    exact h.symm.trans hz
  have tz (a b c : Fin 4) : T a b c = 0 := by
    have h1 := anti a b c
    have h2 := anti a c b
    have h3 := anti b c a
    rw [ts b a c] at h1
    rw [ts c a b, ts a c b] at h2
    linarith
  have qz (i a c : Fin 4) : Q i a c = 0 := by
    have h := canonical_metric_double_contraction (fun j => Q j a c) i
    change (∑ b : Fin 4, metric i b * T b a c) = Q i a c at h
    simpa only [tz, mul_zero, Finset.sum_const_zero] using h.symm
  refine ⟨Fzero, DFzero, ?_⟩
  intro i a
  apply continuousLinearMap_zero_of_coordinate_basis
  intro c
  exact qz i a c

theorem c2_normal_chart_identity_frame_curvature_transport (g : MetricField)
    (germ : C2NormalizedMetricGerm g) (F : CoordinatePoint → CoordinatePoint)
    (regular : ContDiffAt ℝ 3 F 0) (Fzero : F 0 = 0)
    (DFzero : fderiv ℝ F 0 = ContinuousLinearMap.id ℝ CoordinatePoint)
    (normal : ∀ a b, fderiv ℝ (fun x => coordinateMetricPullback g F x a b) 0 = 0) :
    loweredConnectionCurvature (coordinateMetricPullback g F)
      (leviCivitaCoefficients (coordinateMetricPullback g F)) 0 =
        loweredConnectionCurvature g (leviCivitaCoefficients g) 0 :=
  c2_leviCivita_identity_second_jet_transport g germ F regular
    (normal_metric_identity_frame_forces_second_jet g germ F regular Fzero DFzero normal)

#print axioms coordinate_second_partial_symmetric
#print axioms general_identity_first_jet_metric_partial
#print axioms normal_metric_identity_frame_forces_second_jet
#print axioms c2_normal_chart_identity_frame_curvature_transport
end
end AASCSemanticExhaustion
