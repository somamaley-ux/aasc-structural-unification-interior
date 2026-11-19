import EinsteinOriginalCurvatureResponse
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Matrix.Normed

/-! A differential bridge for smooth metric responses. The input to the analytic
step is the vanishing of the second derivative of the response to the normalized
metric Hessian. Smoothness alone does not make that derivative vanish. -/
namespace AASCSemanticExhaustion
noncomputable section
open scoped Matrix.Norms.Elementwise

/-- A response with zero second derivative on a real vector space is its
flat baseline plus its differential there. Both differentiability hypotheses
prevent totalized derivatives from certifying nonsmooth profiles. -/
theorem eq_baseline_add_linear_of_zero_second_derivative
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (F : V → W)
    (hF : Differentiable ℝ F) (hD : Differentiable ℝ (fderiv ℝ F))
    (hDD : ∀ H, fderiv ℝ (fderiv ℝ F) H = 0) (H : V) :
    F H = F 0 + (fderiv ℝ F 0) H := by
  let L := fderiv ℝ F 0
  have slope (x : V) : fderiv ℝ F x = L :=
    is_const_of_fderiv_eq_zero hD hDD x 0
  have hg (x : V) : HasFDerivAt (fun y => F 0 + L y) L x := by
    simpa using (L.hasFDerivAt.const_add (F 0) : HasFDerivAt _ _ x)
  have heq : F = fun y => F 0 + L y := by
    refine eq_of_fderiv_eq hF (fun x => (hg x).differentiableAt) ?_ 0 ?_
    · intro x
      rw [(hg x).fderiv, slope]
    · simp
  exact congrFun heq H

/-- The intrinsic curvature presented by a normalized smooth germ gives
exactly the same response as its canonical Hessian representative. -/
theorem value_on_normal_curvature_representative
    (E : MetricFieldResponse) (hn : RegularLorentzResponseNatural E)
    (hl : RegularLorentzTwoJetLocal E) (g : MetricField)
    (hg : NormalizedSmoothMetricGerm g) :
    E g 0 = metricHessianResponseAt E 0 (normalJetMap (originalNormalizedCurvature g hg)) := by
  let hc := original_smooth_normalized_is_c2 g hg
  let H := c2MetricHessian g 0 hc.1 hc.2.1
  calc
    E g 0 = E (hessianMetricPolynomial H) 0 :=
      hl _ _ 0 (c2_normalized_is_lorentz g hc) (hessian_receiver_is_c2_lorentz H)
        (c2_normalized_metric_matches_receiver g hc)
    _ = metricHessianResponseAt E 0 H := (metricHessianResponseAt_origin E H).symm
    _ = _ := by
      change _ = metricHessianResponseAt E 0 (normalJetMap (c2NormalizedLeviCivitaCurvature g hc))
      rw [c2_normalizedLeviCivitaCurvature_eq_jet]
      exact hessian_response_curvature_factorization _ (regular_lorentz_hessian_gauge E hn hl) H

/-- The zero-Hessian criterion on actual polynomial metric probes discharges
both affine laws on actual normalized curvature, including the metric baseline. -/
theorem original_curvature_affine_of_vanishing_response_hessian
    (E : MetricFieldResponse) (hn : RegularLorentzResponseNatural E)
    (hl : RegularLorentzTwoJetLocal E)
    (hF : Differentiable ℝ (metricHessianResponseAt E 0))
    (hD : Differentiable ℝ (fderiv ℝ (metricHessianResponseAt E 0)))
    (hDD : ∀ H, fderiv ℝ (fderiv ℝ (metricHessianResponseAt E 0)) H = 0) :
    OriginalCurvatureFirstResponse E := by
  let F := metricHessianResponseAt E 0
  let L := fderiv ℝ F 0
  have value (g : MetricField) (hg : NormalizedSmoothMetricGerm g) :
      E g 0 = E flatMetricField 0 + L (normalJetMap (originalNormalizedCurvature g hg)) := by
    rw [value_on_normal_curvature_representative E hn hl g hg]
    simpa only [F, L, metricHessianResponseAt_origin, hessianMetricPolynomial_flat] using
      eq_baseline_add_linear_of_zero_second_derivative F hF hD hDD
        (normalJetMap (originalNormalizedCurvature g hg))
  constructor
  · intro g h k hg hh hk hsum
    rw [value k hk, value g hg, value h hh, hsum, map_add, map_add]
    abel
  · intro r g k hg hk hscale
    rw [value k hk, value g hg, hscale, map_smul, map_smul]
    simp only [add_sub_cancel_left]
    abel

/-- The action-independent geometric classification with an explicit
differential input in place of first curvature response. -/
theorem unique_einstein_of_vanishing_response_hessian
    (E : MetricFieldResponse) (hn : RegularLorentzResponseNatural E)
    (hl : RegularLorentzTwoJetLocal E)
    (hF : Differentiable ℝ (metricHessianResponseAt E 0))
    (hD : Differentiable ℝ (fderiv ℝ (metricHessianResponseAt E 0)))
    (hDD : ∀ H, fderiv ℝ (fderiv ℝ (metricHessianResponseAt E 0)) H = 0)
    (symmetric : ∀ g p, C2LorentzMetricAt g p → ∀ i j, E g p i j = E g p j i)
    (closed : GeneralNormalMetricResponseClosure E) (active : FullLorentzEnvelopeResponseActive E) :
    ∃! ac : ℝ × ℝ, ac.1 ≠ 0 ∧ CoordinateEinsteinResponseForm E ac.1 ac.2 :=
  original_curvature_general_response_has_unique_einstein_form E hn hl
    (original_curvature_affine_of_vanishing_response_hessian E hn hl hF hD hDD)
    symmetric closed active

end
end AASCSemanticExhaustion
