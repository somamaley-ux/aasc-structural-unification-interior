import KGSpectralCauchyFamilies

noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform Topology
namespace AASCKleinGordon

theorem spatialSineSolution_hasDerivAt (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (t : ℝ) (x : KGSpatialSpace) :
    HasDerivAt (fun s => spatialSineSolutionCLM a s f x) (spatialCosineSolutionCLM a t f x) t := by
  apply inverseFourierFamily_hasDerivAt
    (fun s => spatialSineMultiplierCLM a s (𝓕 f)) (fun s => spatialCosineMultiplierCLM a s (𝓕 f))
    (fun ξ => ‖𝓕 f ξ‖) (𝓕 f).integrable.norm
  · intro s ξ
    simp_rw [spatialSineMultiplier_apply,spatialCosineMultiplier_apply]
    exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s
      (spatialSineCoefficient_hasDerivAt a s ξ)).mul_const (𝓕 f ξ)
  · intro s ξ
    rw [spatialCosineMultiplier_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)

theorem spatialCosineSolution_hasDerivAt (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (t : ℝ) (x : KGSpatialSpace) :
    HasDerivAt (fun s => spatialCosineSolutionCLM a s f x) (spatialAccelerationSolutionCLM a t f x) t := by
  apply inverseFourierFamily_hasDerivAt
    (fun s => spatialCosineMultiplierCLM a s (𝓕 f)) (fun s => spatialAccelerationMultiplierCLM a s (𝓕 f))
    (fun ξ => ‖spatialOmegaMultiplierCLM a (𝓕 f) ξ‖) (spatialOmegaMultiplierCLM a (𝓕 f)).integrable.norm
  · intro s ξ
    simp_rw [spatialCosineMultiplier_apply,spatialAccelerationMultiplier_apply]
    exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s
      (temporalShellCosine_hasDerivAt a (spatialSpectralMomentumCLM a ξ) s)).mul_const (𝓕 f ξ)
  · intro s ξ
    rw [spatialAccelerationMultiplier_apply,spatialOmegaMultiplier_apply]
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_neg,
      abs_of_pos (spatialOmega_pos a ξ)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (le_of_lt (spatialOmega_pos a ξ)) (Real.abs_sin_le_one _)) (norm_nonneg _)

theorem spatialSineSolution_initial_velocity (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (x : KGSpatialSpace) :
    HasDerivAt (fun s => spatialSineSolutionCLM a s f x) (f x) 0 := by
  simpa only [spatialCosineSolution_zero] using spatialSineSolution_hasDerivAt a f 0 x

theorem spatialSineSolution_joint_continuous (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) :
    Continuous (fun z : ℝ × KGSpatialSpace => spatialSineSolutionCLM a z.1 f z.2) := by
  apply inverseFourierFamily_joint_continuous (fun t => spatialSineMultiplierCLM a t (𝓕 f))
    (fun ξ => ‖spatialInverseOmegaMultiplierCLM a (𝓕 f) ξ‖)
    (spatialInverseOmegaMultiplierCLM a (𝓕 f)).integrable.norm
  · intro ξ
    simp_rw [spatialSineMultiplier_apply]
    have hc : Continuous (fun t => spatialSineCoefficient a t ξ) :=
      continuous_iff_continuousAt.mpr (fun t => (spatialSineCoefficient_hasDerivAt a t ξ).continuousAt)
    exact (Complex.continuous_ofReal.comp hc).mul continuous_const
  · intro t ξ
    have hp := shellAngularFrequency_pos a (spatialSpectralMomentumCLM a ξ)
    rw [spatialSineMultiplier_apply,spatialInverseOmegaMultiplier_apply]
    simp only [spatialSineCoefficient,sineCauchyCoefficient,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_mul,abs_inv,abs_of_pos (spatialOmega_pos a ξ)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [abs_of_pos hp]
    exact mul_le_of_le_one_left (inv_nonneg.mpr hp.le) (Real.abs_sin_le_one _)

theorem spatialCosineSolution_joint_continuous (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) :
    Continuous (fun z : ℝ × KGSpatialSpace => spatialCosineSolutionCLM a z.1 f z.2) := by
  apply inverseFourierFamily_joint_continuous (fun t => spatialCosineMultiplierCLM a t (𝓕 f))
    (fun ξ => ‖𝓕 f ξ‖) (𝓕 f).integrable.norm
  · intro ξ
    simp_rw [spatialCosineMultiplier_apply]
    have hc : Continuous (fun t => spatialCosineCoefficient a t ξ) :=
      continuous_iff_continuousAt.mpr (fun t =>
        (temporalShellCosine_hasDerivAt a (spatialSpectralMomentumCLM a ξ) t).continuousAt)
    exact (Complex.continuous_ofReal.comp hc).mul continuous_const
  · intro t ξ
    rw [spatialCosineMultiplier_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)

end AASCKleinGordon
