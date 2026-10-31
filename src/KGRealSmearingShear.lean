import KGSpacetimeSmearing
import KGWignerShellNormalization
import KGEnergyBounds
import SchwartzTensorInsertion

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem temperate_pair {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : D → E} {g : D → F} (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) :
    (fun x => (f x,g x)).HasTemperateGrowth := by
  have h:=((ContinuousLinearMap.inl ℝ E F).hasTemperateGrowth.comp hf).add
    ((ContinuousLinearMap.inr ℝ E F).hasTemperateGrowth.comp hg)
  convert h using 1
  funext x
  change (f x,g x)=(f x,0)+(0,g x)
  simp

theorem polynomial_growth_of_temperate_left_inverse {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (h : F → E) (hh : h.HasTemperateGrowth) (hi : ∀ x,h (g x)=x) :
    ∃ (k : ℕ) (C : ℝ),∀ x,‖x‖≤C*(1+‖g x‖)^k := by
  obtain ⟨k,C,hC⟩:=hh.2 0
  refine ⟨k,C,fun x => ?_⟩
  simpa only [norm_iteratedFDeriv_zero,hi] using hC (g x)

/-- Actual frequency coordinates divided by the original wave scale. -/
def unscaledFrequencyCoordinates (a : Parameters) : Spacetime →L[ℝ] (ℝ × Momentum) :=
  (fourierWaveScale a)⁻¹ • fourCoordinateJoin.symm.toContinuousLinearMap

theorem unscaledFrequencyCoordinates_shell (a : Parameters) (p : Momentum) :
    unscaledFrequencyCoordinates a (shellFrequency a p)=(-energy a p/a.speed,p) := by
  simp only [unscaledFrequencyCoordinates,shellFrequency,shellCovector_eq_join,
    ContinuousLinearMap.smul_apply,ContinuousLinearEquiv.coe_coe,map_smul,
    ContinuousLinearEquiv.symm_apply_apply,smul_smul,
    inv_mul_cancel₀ (fourierWaveScale_pos a).ne',mul_inv_cancel₀ (fourierWaveScale_pos a).ne',one_smul]

theorem unscaledFrequencyCoordinates_reconstruct (a : Parameters) (q : Spacetime) :
    fourierWaveScale a • fourCoordinateJoin (unscaledFrequencyCoordinates a q)=q := by
  simp only [unscaledFrequencyCoordinates,ContinuousLinearMap.smul_apply,
    ContinuousLinearEquiv.coe_coe,map_smul,ContinuousLinearEquiv.apply_symm_apply,
    smul_smul,mul_inv_cancel₀ (fourierWaveScale_pos a).ne',one_smul]

def realSmearingShear (a : Parameters) (q : Spacetime) : ℝ × Momentum :=
  ((unscaledFrequencyCoordinates a q).1+energy a (unscaledFrequencyCoordinates a q).2/a.speed,
    (unscaledFrequencyCoordinates a q).2)

def realSmearingShearInv (a : Parameters) (z : ℝ × Momentum) : Spacetime :=
  fourierWaveScale a • fourCoordinateJoin (z.1-energy a z.2/a.speed,z.2)

theorem realSmearingShearInv_left (a : Parameters) (q : Spacetime) :
    realSmearingShearInv a (realSmearingShear a q)=q := by
  simp only [realSmearingShearInv,realSmearingShear,add_sub_cancel_right]
  exact unscaledFrequencyCoordinates_reconstruct a q

theorem realSmearingShear_temperate (a : Parameters) : (realSmearingShear a).HasTemperateGrowth := by
  have h1:=((ContinuousLinearMap.fst ℝ ℝ Momentum).comp
    (unscaledFrequencyCoordinates a)).hasTemperateGrowth
  have h2:=((ContinuousLinearMap.snd ℝ ℝ Momentum).comp
    (unscaledFrequencyCoordinates a)).hasTemperateGrowth
  have he : (fun q : Spacetime => energy a (unscaledFrequencyCoordinates a q).2/a.speed).HasTemperateGrowth := by
    convert (Function.HasTemperateGrowth.const (a.speed⁻¹)).mul ((energy_temperate a).comp h2) using 1
    funext q
    change energy a (unscaledFrequencyCoordinates a q).2/a.speed=
      a.speed⁻¹*energy a (unscaledFrequencyCoordinates a q).2
    ring
  exact temperate_pair (h1.add he) h2

theorem realSmearingShearInv_temperate (a : Parameters) : (realSmearingShearInv a).HasTemperateGrowth := by
  have h1:=(ContinuousLinearMap.fst ℝ ℝ Momentum).hasTemperateGrowth
  have h2:=(ContinuousLinearMap.snd ℝ ℝ Momentum).hasTemperateGrowth
  have he : (fun z : ℝ × Momentum => energy a z.2/a.speed).HasTemperateGrowth := by
    convert (Function.HasTemperateGrowth.const (a.speed⁻¹)).mul ((energy_temperate a).comp h2) using 1
    funext z
    change energy a z.2/a.speed=a.speed⁻¹*energy a z.2
    ring
  exact ((Function.HasTemperateGrowth.const (fourierWaveScale a)).smul
    (fourCoordinateJoin.toContinuousLinearMap.hasTemperateGrowth.comp
      (temperate_pair (h1.sub he) h2)))

def realSmearingShearPullback (a : Parameters) :
    𝓢(ℝ × Momentum,ℂ) →L[ℂ] 𝓢(Spacetime,ℂ) :=
  SchwartzMap.compCLM ℂ (realSmearingShear_temperate a)
    (polynomial_growth_of_temperate_left_inverse _ _ (realSmearingShearInv_temperate a)
      (realSmearingShearInv_left a))

theorem realSmearingShear_shell (a : Parameters) (p : Momentum) :
    realSmearingShear a (shellFrequency a p)=(0,p) := by
  simp only [realSmearingShear,unscaledFrequencyCoordinates_shell,neg_div,neg_add_cancel]

theorem realSmearingShear_reflected_shell (a : Parameters) (p : Momentum) :
    realSmearingShear a (-shellFrequency a p)=(2*energy a p/a.speed,-p) := by
  simp only [realSmearingShear,map_neg,unscaledFrequencyCoordinates_shell,Prod.fst_neg,
    Prod.snd_neg,energy_neg]
  congr 1
  ring

theorem realSmearingShear_reflected_gap (a : Parameters) (p : Momentum) :
    2*a.mass*a.speed≤2*energy a p/a.speed := by
  rw [le_div_iff₀ a.speed_pos]
  nlinarith [energy_ge_rest a p]

end AASCKleinGordon
