import LocalSecondJetComposition

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

theorem local_cubic_metric_pullback_first (g : MetricField)
    (germ : NormalizedSmoothMetricGerm g) (C : Tensor4) (laws : CubicCoordinateLaws C)
    (a b : Fin 4) :
    fderiv ℝ (fun x => coordinateMetricPullback g (cubicCoordinateMap C) x a b) 0 = 0 := by
  have hj (i k : Fin 4) :
      HasFDerivAt (𝕜 := ℝ) (fun x => coordinateJacobian (cubicCoordinateMap C) x i k) 0 0 := by
    simpa only [quadraticDerivative_zero] using cubic_coordinate_jacobian_hasFDerivAt C laws 0 i k
  have hb (i j : Fin 4) : HasFDerivAt (𝕜 := ℝ) (fun x => g (cubicCoordinateMap C x) i j) 0 0 := by
    have hs : ContDiffAt ℝ ⊤ (fun x => g x i j) (cubicCoordinateMap C 0) := by
      simpa only [cubicCoordinateMap_zero] using germ.2.1 i j
    have hh := ((hs.comp 0 (cubicCoordinateMap_smooth C).contDiffAt).differentiableAt
      (by simp)).hasFDerivAt
    have hz := local_scalarFirstJet_comp_zero (fun x => g x i j) (cubicCoordinateMap C)
      (germ.2.1 i j) (cubicCoordinateMap_smooth C).contDiffAt
      (cubicCoordinateMap_zero C) (germ.2.2.2 i j)
    change HasFDerivAt (fun x => g (cubicCoordinateMap C x) i j)
      (fderiv ℝ (fun x => g (cubicCoordinateMap C x) i j) 0) 0 at hh
    rw [hz] at hh
    exact hh
  have ht (i j : Fin 4) := ((hj i a).mul (hb i j)).mul (hj j b)
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => ht i j))
  have hd : HasFDerivAt (𝕜 := ℝ)
      (fun x => coordinateMetricPullback g (cubicCoordinateMap C) x a b) 0 0 := by
    simpa only [coordinateMetricPullback, Pi.mul_apply, zero_smul, smul_zero, add_zero,
      Finset.sum_const_zero] using hs
  exact hd.fderiv

theorem local_cubic_metric_pullback_germ (g : MetricField)
    (germ : NormalizedSmoothMetricGerm g) (C : Tensor4) (laws : CubicCoordinateLaws C) :
    NormalizedSmoothMetricGerm (coordinateMetricPullback g (cubicCoordinateMap C)) := by
  refine ⟨coordinateMetricPullback_symmetric g germ.1 _, ?_, ?_,
    local_cubic_metric_pullback_first g germ C laws⟩
  · apply coordinateMetricPullback_contDiffAt g _ 0 (cubicCoordinateMap_smooth C).contDiffAt
    simpa only [cubicCoordinateMap_zero] using germ.2.1
  · rw [cubic_metric_pullback_value _ C laws, germ.2.2.1]

theorem local_cubic_metric_pullback_second (g : MetricField)
    (germ : NormalizedSmoothMetricGerm g) (C : Tensor4) (laws : CubicCoordinateLaws C)
    (a b c d : Fin 4) :
    scalarSecondPartial (fun x => coordinateMetricPullback g (cubicCoordinateMap C) x a b) 0 c d =
      scalarSecondPartial (fun x => g x a b) 0 c d +
        (∑ i : Fin 4, metric a i * C i b c d) + (∑ i : Fin 4, metric i b * C i a c d) := by
  let J := fun i k x => coordinateJacobian (cubicCoordinateMap C) x i k
  let B := fun i j x => g (cubicCoordinateMap C x) i j
  let W := fun i j x => J i a x * B i j x * J j b x
  have hj (i k : Fin 4) : ContDiffAt ℝ ⊤ (J i k) 0 := (cubic_jacobian_smooth C laws i k).contDiffAt
  have hb (i j : Fin 4) : ContDiffAt ℝ ⊤ (B i j) 0 := by
    have hs : ContDiffAt ℝ ⊤ (fun x => g x i j) (cubicCoordinateMap C 0) := by
      simpa only [cubicCoordinateMap_zero] using germ.2.1 i j
    exact hs.comp 0 (cubicCoordinateMap_smooth C).contDiffAt
  have hw (i j : Fin 4) : ContDiffAt ℝ ⊤ (W i j) 0 := ((hj i a).mul (hb i j)).mul (hj j b)
  have hfirstJ (i k : Fin 4) : fderiv ℝ (J i k) 0 = 0 :=
    cubic_coordinate_jacobian_first_zero C laws i k
  have hfirstB (i j : Fin 4) : fderiv ℝ (B i j) 0 = 0 :=
    local_scalarFirstJet_comp_zero (fun x => g x i j) (cubicCoordinateMap C)
      (germ.2.1 i j) (cubicCoordinateMap_smooth C).contDiffAt
      (cubicCoordinateMap_zero C) (germ.2.2.2 i j)
  have hvalJ (i k : Fin 4) : J i k 0 = (1 : Tensor2) i k :=
    congrArg (fun M : Tensor2 => M i k) (cubic_coordinate_jacobian_zero C laws)
  have hvalB (i j : Fin 4) : B i j 0 = metric i j := by
    dsimp [B]
    rw [cubicCoordinateMap_zero, germ.2.2.1]
  have hsecondJ (i k : Fin 4) : scalarSecondPartial (J i k) 0 c d = C i k c d :=
    cubic_coordinate_jacobian_second C laws i k c d
  have hsecondB (i j : Fin 4) : scalarSecondPartial (B i j) 0 c d =
      scalarSecondPartial (fun x => g x i j) 0 c d :=
    local_scalarSecondPartial_comp_flat_identity (fun x => g x i j) (cubicCoordinateMap C)
      (germ.2.1 i j) (cubicCoordinateMap_smooth C).contDiffAt (cubicCoordinateMap_zero C)
      (cubicCoordinateMap_hasFDerivAt_zero C).fderiv (germ.2.2.2 i j) c d
  have hsecondW (i j : Fin 4) : scalarSecondPartial (W i j) 0 c d =
      (1 : Tensor2) i a * metric i j * C j b c d +
        (1 : Tensor2) i a * (1 : Tensor2) j b * scalarSecondPartial (fun x => g x i j) 0 c d +
          metric i j * (1 : Tensor2) j b * C i a c d := by
    rw [local_scalarSecondPartial_triple_flat (J i a) (B i j) (J j b)
      (hj i a) (hb i j) (hj j b) (hfirstJ i a) (hfirstB i j) (hfirstJ j b) c d]
    rw [hvalJ, hvalJ, hvalB, hsecondJ, hsecondJ, hsecondB]
  have houter (i : Fin 4) : ContDiffAt ℝ ⊤ (fun x => ∑ j, W i j x) 0 :=
    ContDiffAt.sum (fun j _ => hw i j)
  change scalarSecondPartial (fun x => ∑ i : Fin 4, ∑ j : Fin 4, W i j x) 0 c d = _
  rw [local_scalarSecondPartial_sum _ 0 houter c d]
  simp_rw [local_scalarSecondPartial_sum _ 0 (hw _) c d, hsecondW]
  simp [Matrix.one_apply, ite_mul, mul_ite, Finset.sum_add_distrib]
  ring

def loweredCubicCoordinate (C : Tensor4) : Tensor4 := fun a b c d =>
  ∑ i : Fin 4, metric a i * C i b c d

theorem loweredCubicCoordinate_laws (C : Tensor4) (laws : CubicCoordinateLaws C) :
    CubicCoordinateLaws (loweredCubicCoordinate C) := by
  constructor
  · intro a b c d
    unfold loweredCubicCoordinate
    simp_rw [laws.1 _ b c d]
  · intro a b c d
    unfold loweredCubicCoordinate
    simp_rw [laws.2 _ b c d]

theorem local_cubic_metric_hessian_difference_gauge (g : MetricField)
    (germ : NormalizedSmoothMetricGerm g) (C : Tensor4) (laws : CubicCoordinateLaws C) :
    HasCubicCoordinateGauge
      (actualMetricHessian (coordinateMetricPullback g (cubicCoordinateMap C)) 0
        (local_cubic_metric_pullback_germ g germ C laws).1
        (local_cubic_metric_pullback_germ g germ C laws).2.1 -
      actualMetricHessian g 0 germ.1 germ.2.1) := by
  refine ⟨loweredCubicCoordinate C, loweredCubicCoordinate_laws C laws, ?_⟩
  intro a b c d
  change scalarSecondPartial (fun x => coordinateMetricPullback g (cubicCoordinateMap C) x a b) 0 c d -
    scalarSecondPartial (fun x => g x a b) 0 c d = _
  rw [local_cubic_metric_pullback_second g germ C laws]
  have hs (i : Fin 4) : metric i b = metric b i := by
    by_cases h : i = b
    · subst b; rfl
    · simp [metric, h, Ne.symm h]
  simp_rw [hs]
  unfold loweredCubicCoordinate
  ring

/-- The actual connection curvature is unchanged by an actual cubic local
coordinate change with identity first jet and zero second jet. -/
theorem normalized_leviCivita_cubic_transport (g : MetricField)
    (germ : NormalizedSmoothMetricGerm g) (C : Tensor4) (laws : CubicCoordinateLaws C) :
    loweredConnectionCurvature (coordinateMetricPullback g (cubicCoordinateMap C))
      (leviCivitaCoefficients (coordinateMetricPullback g (cubicCoordinateMap C))) 0 =
        loweredConnectionCurvature g (leviCivitaCoefficients g) 0 := by
  let germ' := local_cubic_metric_pullback_germ g germ C laws
  let H := actualMetricHessian g 0 germ.1 germ.2.1
  let K := actualMetricHessian (coordinateMetricPullback g (cubicCoordinateMap C)) 0 germ'.1 germ'.2.1
  have hf : curvatureJetMap (K - H) = 0 :=
    cubic_coordinate_gauge_flat _ (local_cubic_metric_hessian_difference_gauge g germ C laws)
  have heq : curvatureJetMap K = curvatureJetMap H :=
    sub_eq_zero.mp (by simpa only [map_sub] using hf)
  rw [normalized_metric_leviCivita_curvature _ germ', normalized_metric_leviCivita_curvature g germ]
  exact congrArg (fun R : curvatureSpace => (R : Tensor4)) heq

#print axioms local_cubic_metric_pullback_first
#print axioms local_cubic_metric_pullback_germ
#print axioms local_cubic_metric_pullback_second
#print axioms loweredCubicCoordinate_laws
#print axioms local_cubic_metric_hessian_difference_gauge
#print axioms normalized_leviCivita_cubic_transport
end
end AASCSemanticExhaustion
