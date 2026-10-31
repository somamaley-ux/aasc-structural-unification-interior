import NormalChartCurvatureReconstruction

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

def metricChristoffelDerivative (g : MetricField) (p : CoordinatePoint) (a b c : Fin 4) :
    CoordinatePoint →L[ℝ] ℝ :=
  ∑ e : Fin 4, ((g p)⁻¹ a e • metricLowerChristoffelDerivative g p e b c +
    lowerChristoffel g p e b c • fderiv ℝ (fun x => (g x)⁻¹ a e) p)

theorem c2_metric_christoffel_hasFDerivAt (g : MetricField) (p : CoordinatePoint)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (nondegenerate : (g p).det ≠ 0) (a b c : Fin 4) :
    HasFDerivAt (fun x => leviCivitaCoefficients g x a b c)
      (metricChristoffelDerivative g p a b c) p := by
  have hd (e : Fin 4) := (c2_metric_inverse_differentiableAt g p regular nondegenerate a e).hasFDerivAt.mul
    (c2_metric_lowerChristoffel_hasFDerivAt g p regular e b c)
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun e _ => hd e)
  simpa only [leviCivitaCoefficients, metricChristoffelDerivative, Pi.mul_apply] using hs

theorem c2_metric_nondegenerate_eventually (g : MetricField) (p : CoordinatePoint)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (nondegenerate : (g p).det ≠ 0) : ∀ᶠ x in nhds p, (g x).det ≠ 0 :=
  (c2_metric_det_differentiableAt g p regular).continuousAt.eventually_ne nondegenerate

/-- Differentiation of actual metric lowering, proved on the nondegenerate
neighborhood. This retains the first-metric-derivative correction outside normal charts. -/
theorem c2_differentiated_leviCivita_lowering (g : MetricField) (p : CoordinatePoint)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (nondegenerate : (g p).det ≠ 0) (a b c : Fin 4) (v : CoordinatePoint) :
    (∑ e : Fin 4, g p a e * fderiv ℝ (fun x => leviCivitaCoefficients g x e b c) p v) =
      metricLowerChristoffelDerivative g p a b c v -
        (∑ e : Fin 4, fderiv ℝ (fun x => g x a e) p v * leviCivitaCoefficients g p e b c) := by
  have heq : ∀ᶠ x in nhds p,
      (∑ e : Fin 4, g x a e * leviCivitaCoefficients g x e b c) = lowerChristoffel g x a b c :=
    (c2_metric_nondegenerate_eventually g p regular nondegenerate).mono
      (fun x hx => leviCivita_lowering g x hx a b c)
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun e _ =>
    ((regular a e).differentiableAt (by norm_num)).hasFDerivAt.mul
      (c2_metric_christoffel_hasFDerivAt g p regular nondegenerate e b c))
  have hd := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heq
  have hleft := hs.fderiv
  change fderiv ℝ (fun x => ∑ e : Fin 4, g x a e * leviCivitaCoefficients g x e b c) p = _ at hleft
  rw [hleft, (c2_metric_lowerChristoffel_hasFDerivAt g p regular a b c).fderiv] at hd
  have h := congrArg (fun D : CoordinatePoint →L[ℝ] ℝ => D v) hd
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.sum_add_distrib] at h
  have hder (e : Fin 4) : metricChristoffelDerivative g p e b c =
      fderiv ℝ (fun x => leviCivitaCoefficients g x e b c) p :=
    (c2_metric_christoffel_hasFDerivAt g p regular nondegenerate e b c).fderiv.symm
  simp_rw [hder, mul_comm (leviCivitaCoefficients g p _ b c)] at h
  linarith

#print axioms c2_metric_christoffel_hasFDerivAt
#print axioms c2_metric_nondegenerate_eventually
#print axioms c2_differentiated_leviCivita_lowering
end
end AASCSemanticExhaustion
