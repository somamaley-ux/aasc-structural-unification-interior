import QuadraticCoordinateCalculus
import MetricHessianSpace

namespace AASCSemanticExhaustion
noncomputable section
open scoped Topology
set_option maxHeartbeats 0

def hessianRow (H : metricHessianSpace) (a b : Fin 4) : Tensor2 :=
  fun c d => (H : Tensor4) a b c d

def hessianMetricPolynomial (H : metricHessianSpace) (x : Fin 4 → ℝ) : Tensor2 :=
  fun a b => metric a b + quadraticPolynomial (hessianRow H a b) x

theorem hessianMetricPolynomial_zero (H : metricHessianSpace) :
    hessianMetricPolynomial H 0 = metric := by
  ext a b
  simp [hessianMetricPolynomial, quadraticPolynomial_zero]

theorem hessianMetricPolynomial_symmetric (H : metricHessianSpace)
    (x : Fin 4 → ℝ) (a b : Fin 4) :
    hessianMetricPolynomial H x a b = hessianMetricPolynomial H x b a := by
  have hr : hessianRow H a b = hessianRow H b a := by
    ext c d
    exact H.property.1 a b c d
  have hm : metric a b = metric b a := by
    by_cases h : a = b
    · subst b; rfl
    · simp [metric, h, Ne.symm h]
  simp only [hessianMetricPolynomial, hm, hr]

theorem hessianMetricPolynomial_smooth (H : metricHessianSpace) (a b : Fin 4) :
    ContDiff ℝ ⊤ (fun x => hessianMetricPolynomial H x a b) := by
  exact contDiff_const.add (quadraticPolynomial_smooth (hessianRow H a b))

theorem hessianMetricPolynomial_hasFDerivAt (H : metricHessianSpace)
    (x : Fin 4 → ℝ) (a b : Fin 4) :
    HasFDerivAt (fun y => hessianMetricPolynomial H y a b)
      (quadraticDerivative (hessianRow H a b) x) x := by
  simpa only [hessianMetricPolynomial, zero_add, Pi.add_apply] using
    (hasFDerivAt_const (metric a b) x).add (quadraticPolynomial_hasFDerivAt (hessianRow H a b) x)

theorem hessianMetricPolynomial_fderiv (H : metricHessianSpace)
    (x : Fin 4 → ℝ) (a b : Fin 4) :
    fderiv ℝ (fun y => hessianMetricPolynomial H y a b) x =
      quadraticDerivative (hessianRow H a b) x :=
  (hessianMetricPolynomial_hasFDerivAt H x a b).fderiv

theorem hessianMetricPolynomial_first_zero (H : metricHessianSpace) (a b : Fin 4) :
    fderiv ℝ (fun y => hessianMetricPolynomial H y a b) 0 = 0 := by
  rw [hessianMetricPolynomial_fderiv, quadraticDerivative_zero]

theorem hessianMetricPolynomial_second (H : metricHessianSpace) (a b c d : Fin 4) :
    fderiv ℝ (fun x => fderiv ℝ (fun y => hessianMetricPolynomial H y a b) x
      (Pi.single c 1)) 0 (Pi.single d 1) = (H : Tensor4) a b c d := by
  simp_rw [hessianMetricPolynomial_fderiv]
  rw [quadraticDerivative_eval_linear,
    (quadraticSecondDerivative (hessianRow H a b) (Pi.single c 1)).hasFDerivAt.fderiv,
    quadraticSecondDerivative_basis]
  change (1 / 2 : ℝ) * ((H : Tensor4) a b d c + (H : Tensor4) a b c d) = _
  rw [H.property.2 a b d c]
  ring

theorem hessianMetricPolynomial_nonsingular_neighborhood (H : metricHessianSpace) :
    ∃ U : Set (Fin 4 → ℝ), IsOpen U ∧ 0 ∈ U ∧
      ∀ x ∈ U, (hessianMetricPolynomial H x).det ≠ 0 := by
  have hc : Continuous (hessianMetricPolynomial H) :=
    continuous_pi fun a => continuous_pi fun b => (hessianMetricPolynomial_smooth H a b).continuous
  have hn : (hessianMetricPolynomial H 0).det ≠ 0 := by
    rw [hessianMetricPolynomial_zero, canonical_lorentz_metric_det]
    norm_num
  obtain ⟨U, hs, ho, hz⟩ := mem_nhds_iff.mp (hc.matrix_det.continuousAt.eventually_ne hn)
  exact ⟨U, ho, hz, fun x hx => hs hx⟩

theorem hessianMetricPolynomial_normal_agrees (R : curvatureSpace) :
    hessianMetricPolynomial (normalJetMap R) = normalMetricPolynomial R := rfl

#print axioms hessianMetricPolynomial_zero
#print axioms hessianMetricPolynomial_symmetric
#print axioms hessianMetricPolynomial_smooth
#print axioms hessianMetricPolynomial_hasFDerivAt
#print axioms hessianMetricPolynomial_fderiv
#print axioms hessianMetricPolynomial_first_zero
#print axioms hessianMetricPolynomial_second
#print axioms hessianMetricPolynomial_nonsingular_neighborhood
#print axioms hessianMetricPolynomial_normal_agrees
end
end AASCSemanticExhaustion
