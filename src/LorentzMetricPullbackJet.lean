import LorentzMetricComposition
import NormalJetFrameNaturality
import SecondJetComposition

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

theorem matrix_pullback_double_sum (A B : Tensor2) (a b : Fin 4) :
    (∑ i : Fin 4, ∑ j : Fin 4, A i a * B i j * A j b) = (A.transpose * B * A) a b := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem lorentz_metric_pullback_value (H : metricHessianSpace) (L : LorentzComparison) :
    coordinateMetricPullback (hessianMetricPolynomial H) (lorentzCoordinateMap L) 0 = metric := by
  ext a b
  simp only [coordinateMetricPullback, lorentzCoordinateMap_jacobian,
    lorentzCoordinateMap_zero, hessianMetricPolynomial_zero]
  rw [matrix_pullback_double_sum, L.metric_preserved]

theorem lorentz_metric_pullback_first_zero (H : metricHessianSpace) (L : LorentzComparison)
    (a b : Fin 4) :
    fderiv ℝ (fun x => coordinateMetricPullback (hessianMetricPolynomial H)
      (lorentzCoordinateMap L) x a b) 0 = 0 := by
  have hb (i j : Fin 4) : HasFDerivAt (𝕜 := ℝ)
      (fun x => hessianMetricPolynomial H (lorentzCoordinateMap L x) i j) 0 0 := by
    have hz := scalarFirstJet_comp_zero (fun x => hessianMetricPolynomial H x i j)
      (lorentzCoordinateMap L) (hessianMetricPolynomial_smooth H i j) (lorentzCoordinateMap_smooth L)
      (lorentzCoordinateMap_zero L) (hessianMetricPolynomial_first_zero H i j)
    have hs := (hessianMetricPolynomial_smooth H i j).comp (lorentzCoordinateMap_smooth L)
    have hd : HasFDerivAt (fun x => hessianMetricPolynomial H (lorentzCoordinateMap L x) i j)
        (fderiv ℝ (fun x => hessianMetricPolynomial H (lorentzCoordinateMap L x) i j) 0) 0 :=
      (hs.differentiable (by simp) 0).hasFDerivAt
    rw [hz] at hd
    exact hd
  have ht (i j : Fin 4) := ((hb i j).const_mul (L.forward i a)).mul_const (L.forward j b)
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => ht i j))
  have hd : HasFDerivAt (𝕜 := ℝ) (fun x => coordinateMetricPullback (hessianMetricPolynomial H)
      (lorentzCoordinateMap L) x a b) 0 0 := by
    simpa only [coordinateMetricPullback, lorentzCoordinateMap_jacobian,
      smul_zero, Finset.sum_const_zero] using hs
  exact hd.fderiv

theorem lorentz_metric_pullback_second (H : metricHessianSpace) (L : LorentzComparison)
    (a b c d : Fin 4) :
    scalarSecondPartial (fun x => coordinateMetricPullback (hessianMetricPolynomial H)
      (lorentzCoordinateMap L) x a b) 0 c d = pullbackFour L.forward H a b c d := by
  let B := fun i j x => hessianMetricPolynomial H (lorentzCoordinateMap L x) i j
  let W := fun i j x => L.forward i a * B i j x * L.forward j b
  have hb (i j : Fin 4) : ContDiff ℝ ⊤ (B i j) :=
    (hessianMetricPolynomial_smooth H i j).comp (lorentzCoordinateMap_smooth L)
  have hw (i j : Fin 4) : ContDiff ℝ ⊤ (W i j) := (contDiff_const.mul (hb i j)).mul contDiff_const
  have hfB (i j : Fin 4) : fderiv ℝ (B i j) 0 = 0 :=
    scalarFirstJet_comp_zero (fun x => hessianMetricPolynomial H x i j) (lorentzCoordinateMap L)
      (hessianMetricPolynomial_smooth H i j) (lorentzCoordinateMap_smooth L)
      (lorentzCoordinateMap_zero L) (hessianMetricPolynomial_first_zero H i j)
  have hc (r : ℝ) : scalarSecondPartial (fun _ : CoordinatePoint => r) 0 c d = 0 := by
    simp [scalarSecondPartial, scalarPartial]
  have hsecond (i j : Fin 4) : scalarSecondPartial (W i j) 0 c d =
      L.forward i a * L.forward j b *
        (∑ u : Fin 4, ∑ v : Fin 4, (H : Tensor4) i j u v * L.forward u c * L.forward v d) := by
    have hf0 : fderiv ℝ (fun _ : CoordinatePoint => L.forward i a) 0 = 0 := by simp
    have hk0 : fderiv ℝ (fun _ : CoordinatePoint => L.forward j b) 0 = 0 := by simp
    have ht := smooth_scalarSecondPartial_triple_flat (fun _ => L.forward i a) (B i j)
      (fun _ => L.forward j b) contDiff_const (hb i j) contDiff_const
      hf0 (hfB i j) hk0 c d
    simp only [hc, mul_zero, zero_mul, zero_add, add_zero] at ht
    change scalarSecondPartial (W i j) 0 c d = _ at ht
    rw [hessian_metric_lorentz_composition_second H L i j c d] at ht
    exact ht
  have houter (i : Fin 4) : ContDiff ℝ ⊤ (fun x => ∑ j, W i j x) :=
    ContDiff.sum (fun j _ => hw i j)
  have heq : (fun x => coordinateMetricPullback (hessianMetricPolynomial H)
      (lorentzCoordinateMap L) x a b) = (fun x => ∑ i : Fin 4, ∑ j : Fin 4, W i j x) := by
    funext x
    simp only [coordinateMetricPullback, lorentzCoordinateMap_jacobian, W, B]
  rw [heq, smooth_scalarSecondPartial_sum _ houter c d]
  simp_rw [smooth_scalarSecondPartial_sum _ (hw _) c d, hsecond]
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
  ring

#print axioms matrix_pullback_double_sum
#print axioms lorentz_metric_pullback_value
#print axioms lorentz_metric_pullback_first_zero
#print axioms lorentz_metric_pullback_second
end
end AASCSemanticExhaustion
