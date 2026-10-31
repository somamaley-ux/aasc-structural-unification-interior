import KGShellToSineIdentity
import KGSpacetimeSliceCausalGap

noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

/-- Causal support of the original positive-minus-negative Wigner shell functional.
The support conclusion follows from the proved sine-family PDE and energy estimate;
no causal-support certificate is received. -/
theorem massShellCommutator_causal_support (a : Parameters) (h : 𝓢(Spacetime,ℂ))
    (hc : HasCompactSupport (h : Spacetime → ℂ))
    (hs : Disjoint (tsupport (h : Spacetime → ℂ)) closedCausalCone) :
    massShellCommutatorCLM a h=0 := by
  rw [massShellCommutator_eq_sine_time_integral a h hc]
  have hz : (∫ t : ℝ, spatialSineSolutionCLM a t (spacetimeSpatialSliceCLM t h) 0)=0 := by
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall fun t => spatialSineSlice_origin_zero_off_causal_cone a h hc hs t
  rw [hz,mul_zero]

theorem originalShell_correlation_vanishes_of_spacelike (a : Parameters)
    (h k : 𝓢(Spacetime,ℂ)) (hh : HasCompactSupport (h : Spacetime → ℂ))
    (hk : HasCompactSupport (k : Spacetime → ℂ)) (hs : SpacelikeSeparatedTests h k) :
    massShellCommutatorCLM a (commutatorCorrelationTest h k)=0 :=
  massShellCommutator_causal_support a (commutatorCorrelationTest h k)
    (commutatorCorrelation_compact_support h k hh hk)
    (commutatorCorrelation_causally_disjoint h k hh hk hs)

/-- Locality on the original finite-particle Schwartz field core, with the original
field normalization s. No replacement field, zero distribution or smaller core. -/
theorem spacetimeFieldCore_locality (a : Parameters) (s : ℝ)
    (h k : 𝓢(Spacetime,ℂ)) (hh : HasCompactSupport (h : Spacetime → ℂ))
    (hk : HasCompactSupport (k : Spacetime → ℂ)) (hs : SpacelikeSeparatedTests h k) :
    (spacetimeFieldCore a s h).comp (spacetimeFieldCore a s k)=
      (spacetimeFieldCore a s k).comp (spacetimeFieldCore a s h) := by
  rw [spacetimeFieldCore_CCR_spectral,originalShell_correlation_vanishes_of_spacelike a h k hh hk hs]
  simp only [mul_zero,zero_smul,add_zero]

theorem fieldCommutatorCoefficient_zero_of_spacelike (a : Parameters) (s : ℝ)
    (h k : 𝓢(Spacetime,ℂ)) (hh : HasCompactSupport (h : Spacetime → ℂ))
    (hk : HasCompactSupport (k : Spacetime → ℂ)) (hs : SpacelikeSeparatedTests h k) :
    fieldCommutatorCoefficient a s h k=0 := by
  rw [fieldCommutatorCoefficient_eq_spectral_distribution,
    originalShell_correlation_vanishes_of_spacelike a h k hh hk hs,mul_zero]

end AASCKleinGordon
