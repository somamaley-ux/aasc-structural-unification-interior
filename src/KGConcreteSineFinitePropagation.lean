import KGConcreteProjectedSolution

noncomputable section
set_option maxHeartbeats 1400000
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

theorem massWaveNumber_ne_zero (a : Parameters) : massWaveNumber a ≠ 0 := by
  unfold massWaveNumber
  exact div_ne_zero (mul_ne_zero (ne_of_gt a.mass_pos) (ne_of_gt a.speed_pos)) (ne_of_gt a.hbar_pos)

theorem projectedSine_vanishes_forward
    (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ)
    (R t : ℝ) (x₀ : KGSpatialSpace) (ht : 0 ≤ t) (hRt : t < R)
    (hf : ∀ x ∈ Metric.closedBall x₀ R, f x=0) :
    P (spatialSineSolutionCLM a t f x₀)=0 := by
  apply (concreteProjectedSineSolution a f P).vanishes_inside_forward_cone (massWaveNumber_ne_zero a) R t x₀ ht hRt
  intro x hx
  refine ⟨concreteProjectedSine_initial_position a f P x,?_,concreteProjectedSine_initial_gradient a f P x⟩
  rw [concreteProjectedSine_initial_velocity,hf x hx,P.map_zero]

/-- The generic energy theorem is now applied to both actual components of the
exact complex Fourier sine family; no finite-propagation witness is assumed. -/
theorem spatialSineSolution_vanishes_forward
    (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ))
    (R t : ℝ) (x₀ : KGSpatialSpace) (ht : 0 ≤ t) (hRt : t < R)
    (hf : ∀ x ∈ Metric.closedBall x₀ R, f x=0) :
    spatialSineSolutionCLM a t f x₀=0 := by
  apply Complex.ext
  · exact projectedSine_vanishes_forward a f Complex.reCLM R t x₀ ht hRt hf
  · exact projectedSine_vanishes_forward a f Complex.imCLM R t x₀ ht hRt hf

theorem spatialSineSolution_neg_time (a : Parameters) (t : ℝ) (f : 𝓢(KGSpatialSpace,ℂ)) :
    spatialSineSolutionCLM a (-t) f= -spatialSineSolutionCLM a t f := by
  apply spatialFourier_injective
  ext ξ
  simp only [FourierTransform.fourier_neg,SchwartzMap.neg_apply,fourier_spatialSineSolution]
  simp [spatialSineCoefficient,sineCauchyCoefficient,temporalShellSine,mul_neg,Real.sin_neg]

theorem spatialSineSolution_vanishes_of_abs_time_lt
    (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (R t : ℝ) (x₀ : KGSpatialSpace)
    (hRt : |t| < R) (hf : ∀ x ∈ Metric.closedBall x₀ R, f x=0) :
    spatialSineSolutionCLM a t f x₀=0 := by
  by_cases ht : 0 ≤ t
  · exact spatialSineSolution_vanishes_forward a f R t x₀ ht ((le_abs_self t).trans_lt hRt) hf
  · have hn : 0 ≤ -t := le_of_lt (neg_pos.mpr (lt_of_not_ge ht))
    have hz := spatialSineSolution_vanishes_forward a f R (-t) x₀ hn ((neg_le_abs t).trans_lt hRt) hf
    rw [spatialSineSolution_neg_time,SchwartzMap.neg_apply,neg_eq_zero] at hz
    exact hz

end AASCKleinGordon
