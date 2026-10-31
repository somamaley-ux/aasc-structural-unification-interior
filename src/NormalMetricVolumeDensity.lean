import NormalMetricInverseJet
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Mul

namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def coordinateVolumeDensity (g : MetricField) (p : CoordinatePoint) : ℝ :=
  Real.sqrt (-(g p).det)

theorem c2_normal_metric_determinant_hasFDerivAt_zero (g : MetricField)
    (germ : C2NormalizedMetricGerm g) : HasFDerivAt (𝕜 := ℝ) (fun x => (g x).det) 0 0 := by
  have hf (a b : Fin 4) : HasFDerivAt (fun x => g x a b) (0 : CoordinatePoint →L[ℝ] ℝ) 0 := by
    have hd := ((germ.2.1 a b).differentiableAt (by norm_num)).hasFDerivAt
    simpa only [germ.2.2.2] using hd
  have hp (σ : Equiv.Perm (Fin 4)) :
      HasFDerivAt (fun x => ∏ i : Fin 4, g x (σ i) i) (0 : CoordinatePoint →L[ℝ] ℝ) 0 := by
    have hd := HasFDerivAt.finset_prod (u := Finset.univ) (fun i _ => hf (σ i) i)
    simpa only [smul_zero, Finset.sum_const_zero] using hd
  have hd := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun (σ : Equiv.Perm (Fin 4)) _ => (hp σ).const_mul ((σ.sign : ℤ) : ℝ))
  simpa only [Matrix.det_apply', smul_zero, Finset.sum_const_zero] using hd

theorem c2_normal_metric_volume_value (g : MetricField) (germ : C2NormalizedMetricGerm g) :
    coordinateVolumeDensity g 0 = 1 := by
  simp [coordinateVolumeDensity, germ.2.2.1, canonical_lorentz_metric_det]

theorem c2_normal_metric_volume_hasFDerivAt_zero (g : MetricField)
    (germ : C2NormalizedMetricGerm g) : HasFDerivAt (𝕜 := ℝ) (coordinateVolumeDensity g) 0 0 := by
  have hvalue : -(g 0).det = 1 := by rw [germ.2.2.1, canonical_lorentz_metric_det]; norm_num
  have hs := Real.hasDerivAt_sqrt (show -(g 0).det ≠ 0 by rw [hvalue]; norm_num)
  have hd := hs.hasFDerivAt.comp (0 : CoordinatePoint) (c2_normal_metric_determinant_hasFDerivAt_zero g germ).neg
  simpa only [coordinateVolumeDensity, ContinuousLinearMap.comp_zero, neg_zero, Function.comp_def] using hd

#print axioms c2_normal_metric_determinant_hasFDerivAt_zero
#print axioms c2_normal_metric_volume_value
#print axioms c2_normal_metric_volume_hasFDerivAt_zero
end
end AASCSemanticExhaustion
