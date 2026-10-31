import KGLorentzBoostShell
import KGSpacetimeSmearing

noncomputable section
open scoped SchwartzMap
namespace AASCKleinGordon

def fourTimeInjection : ℝ →L[ℝ] FourMomentum :=
  fourCoordinateCons.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ ℝ Momentum)

def fourSpatialInjection : Momentum →L[ℝ] FourMomentum :=
  fourCoordinateCons.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ ℝ Momentum)

def fourSpatialProjection : FourMomentum →L[ℝ] Momentum :=
  (ContinuousLinearMap.snd ℝ ℝ Momentum).comp fourCoordinateCons.symm.toContinuousLinearMap

theorem massShell_eq_injections (a : Parameters) (p : Momentum) :
    massShell a p = fourTimeInjection (energy a p/a.speed) + fourSpatialInjection p := by
  ext i
  fin_cases i
  · change energy a p/a.speed = energy a p/a.speed + 0
    exact (add_zero _).symm
  · change p 0 = 0 + p 0
    exact (zero_add _).symm
  · change p 1 = 0 + p 1
    exact (zero_add _).symm
  · change p 2 = 0 + p 2
    exact (zero_add _).symm

theorem massShell_temperate (a : Parameters) : (massShell a).HasTemperateGrowth := by
  have he : (fun p => energy a p/a.speed).HasTemperateGrowth := by
    convert (energy_temperate a).mul (Function.HasTemperateGrowth.const a.speed⁻¹) using 1
  have h := (fourTimeInjection.hasTemperateGrowth.comp he).add fourSpatialInjection.hasTemperateGrowth
  convert h using 1
  funext p
  exact massShell_eq_injections a p

theorem axisBoostMomentum_eq_projection (a : Parameters) (r : ℝ) (p : Momentum) :
    axisBoostMomentum a r p = fourSpatialProjection (axisBoostFourCLE r (massShell a p)) := by
  ext i
  fin_cases i <;> rfl

theorem axisBoostMomentum_temperate (a : Parameters) (r : ℝ) :
    (axisBoostMomentum a r).HasTemperateGrowth := by
  have h := fourSpatialProjection.hasTemperateGrowth.comp
    ((axisBoostFourCLE r).toContinuousLinearMap.hasTemperateGrowth.comp (massShell_temperate a))
  convert h using 1

theorem axisBoostMomentum_polynomial_inverse_bound (a : Parameters) (r : ℝ) :
    ∃ (k : ℕ) (C : ℝ), ∀ p, ‖p‖ ≤ C*(1+‖axisBoostMomentum a r p‖)^k := by
  obtain ⟨k,C,h⟩ := (axisBoostMomentum_temperate a (-r)).2 0
  refine ⟨k,C,fun p => ?_⟩
  simpa only [norm_iteratedFDeriv_zero, axisBoostMomentum_neg_inverse] using
    h (axisBoostMomentum a r p)

def axisBoostSchwartzCLM (a : Parameters) (r : ℝ) : 𝓢(Momentum,ℂ) →L[ℂ] 𝓢(Momentum,ℂ) :=
  SchwartzMap.compCLM ℂ (axisBoostMomentum_temperate a (-r))
    (axisBoostMomentum_polynomial_inverse_bound a (-r))

@[simp] theorem axisBoostSchwartzCLM_apply (a : Parameters) (r : ℝ)
    (f : 𝓢(Momentum,ℂ)) (p : Momentum) :
    axisBoostSchwartzCLM a r f p = f (axisBoostMomentum a (-r) p) := rfl

theorem axisBoostSchwartz_inverse (a : Parameters) (r : ℝ) (f : 𝓢(Momentum,ℂ)) :
    axisBoostSchwartzCLM a (-r) (axisBoostSchwartzCLM a r f) = f := by
  ext p
  simp only [axisBoostSchwartzCLM_apply, neg_neg, axisBoostMomentum_neg_inverse]

def axisBoostSchwartzCLE (a : Parameters) (r : ℝ) : 𝓢(Momentum,ℂ) ≃L[ℂ] 𝓢(Momentum,ℂ) where
  toLinearEquiv :=
    { toLinearMap := (axisBoostSchwartzCLM a r).toLinearMap
      invFun := axisBoostSchwartzCLM a (-r)
      left_inv := axisBoostSchwartz_inverse a r
      right_inv := by intro f; simpa only [neg_neg] using axisBoostSchwartz_inverse a (-r) f }
  continuous_toFun := (axisBoostSchwartzCLM a r).continuous
  continuous_invFun := (axisBoostSchwartzCLM a (-r)).continuous

end AASCKleinGordon
