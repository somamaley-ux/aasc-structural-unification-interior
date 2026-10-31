import KGSpatialSineFamily
import Mathlib.Analysis.Calculus.ParametricIntegral

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform Topology
namespace AASCKleinGordon

theorem spatialSineSolution_origin_hasDerivAt
    (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (t : ℝ) :
    HasDerivAt (fun s => spatialSineSolutionCLM a s f 0)
      (∫ ξ : KGSpatialSpace,
        (temporalShellCosine a t (spatialSpectralMomentumCLM a ξ) : ℂ)*𝓕 f ξ) t := by
  simp_rw [spatialSineSolution_at_origin]
  have hc (s : ℝ) : Continuous (fun ξ : KGSpatialSpace =>
      (temporalShellCosine a s (spatialSpectralMomentumCLM a ξ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((temporalShellCosine_temperate a s).1.continuous.comp
      (spatialSpectralMomentumCLM a).continuous)
  have hi (s : ℝ) : Integrable (fun ξ : KGSpatialSpace =>
      (spatialSineCoefficient a s ξ : ℂ)*𝓕 f ξ) := by
    simpa only [← spatialSineMultiplier_apply] using
      (spatialSineMultiplierCLM a s (𝓕 f)).integrable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (x₀ := t)
    (F := fun s ξ => (spatialSineCoefficient a s ξ : ℂ)*𝓕 f ξ)
    (F' := fun s ξ => (temporalShellCosine a s (spatialSpectralMomentumCLM a ξ) : ℂ)*𝓕 f ξ)
    (bound := fun ξ => ‖𝓕 f ξ‖) univ_mem
    (Eventually.of_forall fun s => (hi s).aestronglyMeasurable) (hi t)
    ((hc t).mul (𝓕 f).continuous).aestronglyMeasurable ?_ (𝓕 f).integrable.norm ?_).2
  · exact Eventually.of_forall fun ξ s _ => by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)
  · exact Eventually.of_forall fun ξ s _ => by
      have hd := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s
        (spatialSineCoefficient_hasDerivAt a s ξ)
      exact hd.mul_const (𝓕 f ξ)

theorem spatialFourierIntegral_eq_value_zero (f : 𝓢(KGSpatialSpace,ℂ)) :
    (∫ ξ : KGSpatialSpace, 𝓕 f ξ)=f 0 := by
  have hi := congrArg (fun g : 𝓢(KGSpatialSpace,ℂ) => g 0)
    (FourierTransform.fourierInv_fourier_eq (F := 𝓢(KGSpatialSpace,ℂ)) f)
  change (𝓕⁻ (𝓕 f)) 0=f 0 at hi
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq] at hi
  simpa only [inner_zero_right,Real.fourierChar.map_zero_eq_one,one_smul] using hi

theorem spatialSineSolution_initial_velocity_origin (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) :
    HasDerivAt (fun s => spatialSineSolutionCLM a s f 0) (f 0) 0 := by
  simpa only [temporalShellCosine_zero,Complex.ofReal_one,one_mul,spatialFourierIntegral_eq_value_zero]
    using spatialSineSolution_origin_hasDerivAt a f 0

end AASCKleinGordon
