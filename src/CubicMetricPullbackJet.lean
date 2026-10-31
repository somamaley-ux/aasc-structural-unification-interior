import SecondJetComposition
import ScalarSmoothJetRules

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

theorem cubic_jacobian_smooth (C : Tensor4) (laws : CubicCoordinateLaws C) (i a : Fin 4) :
    ContDiff ℝ ⊤ (fun x => coordinateJacobian (cubicCoordinateMap C) x i a) := by
  have heq : (fun x => coordinateJacobian (cubicCoordinateMap C) x i a) =
      (fun x => (1 : Tensor2) i a + quadraticPolynomial (fun b c => C i a b c) x) :=
    funext (fun x => cubic_coordinate_jacobian_formula C laws x i a)
  rw [heq]
  exact contDiff_const.add (quadraticPolynomial_smooth _)

theorem cubic_metric_pullback_value (g : MetricField) (C : Tensor4) (laws : CubicCoordinateLaws C) :
    coordinateMetricPullback g (cubicCoordinateMap C) 0 = g 0 := by
  ext a b
  simp [coordinateMetricPullback, cubic_coordinate_jacobian_zero C laws,
    cubicCoordinateMap_zero, Matrix.one_apply, ite_mul, mul_ite]

theorem cubic_metric_pullback_hasFDerivAt_zero (g : MetricField)
    (smooth : ∀ a b, ContDiff ℝ ⊤ (fun x => g x a b))
    (first : ∀ a b, fderiv ℝ (fun x => g x a b) 0 = 0)
    (C : Tensor4) (laws : CubicCoordinateLaws C) (a b : Fin 4) :
    HasFDerivAt (𝕜 := ℝ) (fun x => coordinateMetricPullback g (cubicCoordinateMap C) x a b) 0 0 := by
  have hj (i k : Fin 4) :
      HasFDerivAt (𝕜 := ℝ) (fun x => coordinateJacobian (cubicCoordinateMap C) x i k) 0 0 := by
    simpa only [quadraticDerivative_zero] using cubic_coordinate_jacobian_hasFDerivAt C laws 0 i k
  have hb (i j : Fin 4) : HasFDerivAt (𝕜 := ℝ) (fun x => g (cubicCoordinateMap C x) i j) 0 0 := by
    have hd := scalarFirstJet_comp_zero (fun x => g x i j) (cubicCoordinateMap C)
      (smooth i j) (cubicCoordinateMap_smooth C) (cubicCoordinateMap_zero C) (first i j)
    have hs := (smooth i j).comp (cubicCoordinateMap_smooth C)
    have hh : HasFDerivAt (fun x => g (cubicCoordinateMap C x) i j)
        (fderiv ℝ (fun x => g (cubicCoordinateMap C x) i j) 0) 0 :=
      (hs.differentiable (by simp) 0).hasFDerivAt
    rw [hd] at hh
    exact hh
  have ht (i j : Fin 4) := ((hj i a).mul (hb i j)).mul (hj j b)
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => ht i j))
  simpa only [coordinateMetricPullback, Pi.mul_apply, zero_smul, smul_zero, add_zero,
    Finset.sum_const_zero] using hsum

theorem cubic_metric_pullback_first_zero (g : MetricField)
    (smooth : ∀ a b, ContDiff ℝ ⊤ (fun x => g x a b))
    (first : ∀ a b, fderiv ℝ (fun x => g x a b) 0 = 0)
    (C : Tensor4) (laws : CubicCoordinateLaws C) (a b : Fin 4) :
    fderiv ℝ (fun x => coordinateMetricPullback g (cubicCoordinateMap C) x a b) 0 = 0 :=
  (cubic_metric_pullback_hasFDerivAt_zero g smooth first C laws a b).fderiv

theorem cubic_metric_pullback_second (g : MetricField)
    (smooth : ∀ a b, ContDiff ℝ ⊤ (fun x => g x a b))
    (value : g 0 = metric) (first : ∀ a b, fderiv ℝ (fun x => g x a b) 0 = 0)
    (C : Tensor4) (laws : CubicCoordinateLaws C) (a b c d : Fin 4) :
    scalarSecondPartial (fun x => coordinateMetricPullback g (cubicCoordinateMap C) x a b) 0 c d =
      scalarSecondPartial (fun x => g x a b) 0 c d +
        (∑ i : Fin 4, metric a i * C i b c d) + (∑ i : Fin 4, metric i b * C i a c d) := by
  let J := fun i k x => coordinateJacobian (cubicCoordinateMap C) x i k
  let B := fun i j x => g (cubicCoordinateMap C x) i j
  let W := fun i j x => J i a x * B i j x * J j b x
  have hj (i k : Fin 4) : ContDiff ℝ ⊤ (J i k) := cubic_jacobian_smooth C laws i k
  have hb (i j : Fin 4) : ContDiff ℝ ⊤ (B i j) := (smooth i j).comp (cubicCoordinateMap_smooth C)
  have hw (i j : Fin 4) : ContDiff ℝ ⊤ (W i j) := ((hj i a).mul (hb i j)).mul (hj j b)
  have hfirstJ (i k : Fin 4) : fderiv ℝ (J i k) 0 = 0 :=
    cubic_coordinate_jacobian_first_zero C laws i k
  have hfirstB (i j : Fin 4) : fderiv ℝ (B i j) 0 = 0 :=
    scalarFirstJet_comp_zero (fun x => g x i j) (cubicCoordinateMap C)
      (smooth i j) (cubicCoordinateMap_smooth C) (cubicCoordinateMap_zero C) (first i j)
  have hvalJ (i k : Fin 4) : J i k 0 = (1 : Tensor2) i k :=
    congrArg (fun M : Tensor2 => M i k) (cubic_coordinate_jacobian_zero C laws)
  have hvalB (i j : Fin 4) : B i j 0 = metric i j := by
    dsimp [B]
    rw [cubicCoordinateMap_zero, value]
  have hsecondJ (i k : Fin 4) : scalarSecondPartial (J i k) 0 c d = C i k c d :=
    cubic_coordinate_jacobian_second C laws i k c d
  have hsecondB (i j : Fin 4) : scalarSecondPartial (B i j) 0 c d =
      scalarSecondPartial (fun x => g x i j) 0 c d :=
    scalarSecondJet_comp_identity (fun x => g x i j) (cubicCoordinateMap C)
      (smooth i j) (cubicCoordinateMap_smooth C) (cubicCoordinateMap_zero C)
      (cubicCoordinateMap_hasFDerivAt_zero C).fderiv (first i j) c d
  have hsecondW (i j : Fin 4) : scalarSecondPartial (W i j) 0 c d =
      (1 : Tensor2) i a * metric i j * C j b c d +
        (1 : Tensor2) i a * (1 : Tensor2) j b * scalarSecondPartial (fun x => g x i j) 0 c d +
          metric i j * (1 : Tensor2) j b * C i a c d := by
    rw [smooth_scalarSecondPartial_triple_flat (J i a) (B i j) (J j b)
      (hj i a) (hb i j) (hj j b) (hfirstJ i a) (hfirstB i j) (hfirstJ j b) c d]
    rw [hvalJ, hvalJ, hvalB, hsecondJ, hsecondJ, hsecondB]
  have houter (i : Fin 4) : ContDiff ℝ ⊤ (fun x => ∑ j, W i j x) := by
    apply ContDiff.sum
    intro j _
    exact hw i j
  change scalarSecondPartial (fun x => ∑ i : Fin 4, ∑ j : Fin 4, W i j x) 0 c d = _
  rw [smooth_scalarSecondPartial_sum _ houter c d]
  simp_rw [smooth_scalarSecondPartial_sum _ (hw _) c d, hsecondW]
  simp [Matrix.one_apply, ite_mul, mul_ite, Finset.sum_add_distrib]
  ring

#print axioms cubic_jacobian_smooth
#print axioms cubic_metric_pullback_value
#print axioms cubic_metric_pullback_hasFDerivAt_zero
#print axioms cubic_metric_pullback_first_zero
#print axioms cubic_metric_pullback_second
end
end AASCSemanticExhaustion
