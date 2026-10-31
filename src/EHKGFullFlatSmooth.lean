import EHKGFourierMomentSmooth

/-! Joint smoothness of the actual full Fourier Cauchy family. The phase-graph
representation is proved, including the original cycles-frequency constants. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform Topology
namespace AASCKleinGordon.CurvedKG

theorem homogeneous_phase_frequency_join (a : Parameters) (sign : ℝ) (xi : KGSpatialSpace) :
    homogeneousPhaseFrequency a sign xi =
      spacetimeSpatialJoin (-(sign / (2 * Real.pi)) * spatialOmega a xi, -xi) := by
  change fourCoordinateJoin (-(sign / (2 * Real.pi)) * spatialOmega a xi, 0) -
    fourCoordinateJoin (0, momentumEuclidean.symm xi) = _
  rw [← map_sub]
  simp [spacetimeSpatialJoin]

theorem homogeneous_phase_integrand (a : Parameters) (sign t : ℝ) (x xi : KGSpatialSpace)
    (G : 𝓢(KGSpatialSpace, ℂ)) :
    Real.fourierChar (-inner ℝ (spacetimeSpatialJoin (t, x)) (homogeneousPhaseFrequency a sign xi)) • G xi =
      spatialFourierKernel x xi *
        temporalFourierKernel (-(sign / (2 * Real.pi)) * spatialOmega a xi) t * G xi := by
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  rw [show (2 * Real.pi * (-inner ℝ (spacetimeSpatialJoin (t, x))
      (homogeneousPhaseFrequency a sign xi))) =
    -2 * Real.pi * inner ℝ (spacetimeSpatialJoin (t, x)) (homogeneousPhaseFrequency a sign xi) by ring]
  rw [homogeneous_phase_frequency_join, spacetimeFourierKernel_split]
  simp only [neg_neg]
  have symmetric : spatialFourierKernel xi x = spatialFourierKernel x xi := by
    simp only [spatialFourierKernel, real_inner_comm xi x]
  rw [symmetric]
  ring

theorem homogeneous_phase_integrable (a : Parameters) (sign : ℝ)
    (G : 𝓢(KGSpatialSpace, ℂ)) (t : ℝ) (x : KGSpatialSpace) :
    Integrable (fun xi => Real.fourierChar
      (-inner ℝ (spacetimeSpatialJoin (t, x)) (homogeneousPhaseFrequency a sign xi)) • G xi) := by
  apply G.integrable.mono
  · exact ((Real.continuous_fourierChar.comp
      ((continuous_const.inner (homogeneous_phase_frequency_temperate a sign).1.continuous).neg)).smul
        G.continuous).aestronglyMeasurable
  · exact ae_of_all _ fun z => (Circle.norm_smul _ _).le

theorem cosine_phase_average (a : Parameters) (G : 𝓢(KGSpatialSpace, ℂ))
    (t : ℝ) (x : KGSpatialSpace) :
    (1 / 2 : ℂ) *
      (volumePhaseIntegral (homogeneousPhaseFrequency a 1) G (spacetimeSpatialJoin (t, x)) +
       volumePhaseIntegral (homogeneousPhaseFrequency a (-1)) G (spacetimeSpatialJoin (t, x))) =
      (𝓕⁻ (spatialCosineMultiplierCLM a t G)) x := by
  rw [spatialInverseFourier_apply]
  unfold volumePhaseIntegral
  rw [← integral_add (homogeneous_phase_integrable a 1 G t x)
    (homogeneous_phase_integrable a (-1) G t x), ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun xi => by
    dsimp only
    rw [homogeneous_phase_integrand, homogeneous_phase_integrand, spatialCosineMultiplier_apply]
    have minus : -(1 / (2 * Real.pi)) * spatialOmega a xi = -spatialOmega a xi / (2 * Real.pi) := by ring
    have plus : -((-1) / (2 * Real.pi)) * spatialOmega a xi = spatialOmega a xi / (2 * Real.pi) := by ring
    rw [minus, plus, temporalFourierKernel_shell_minus, temporalFourierKernel_shell_plus]
    simp only [spatialCosineCoefficient, temporalShellCosine, spatialOmega,
      Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring

theorem sine_phase_difference (a : Parameters) (G : 𝓢(KGSpatialSpace, ℂ))
    (t : ℝ) (x : KGSpatialSpace) :
    (2 * Complex.I)⁻¹ *
      (volumePhaseIntegral (homogeneousPhaseFrequency a 1) (spatialInverseOmegaMultiplierCLM a G)
        (spacetimeSpatialJoin (t, x)) -
       volumePhaseIntegral (homogeneousPhaseFrequency a (-1)) (spatialInverseOmegaMultiplierCLM a G)
        (spacetimeSpatialJoin (t, x))) =
      (𝓕⁻ (spatialSineMultiplierCLM a t G)) x := by
  rw [spatialInverseFourier_apply]
  unfold volumePhaseIntegral
  rw [← integral_sub (homogeneous_phase_integrable a 1 _ t x)
    (homogeneous_phase_integrable a (-1) _ t x), ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun xi => by
    dsimp only
    rw [homogeneous_phase_integrand, homogeneous_phase_integrand,
      spatialSineMultiplier_apply, spatialInverseOmegaMultiplier_apply]
    have minus : -(1 / (2 * Real.pi)) * spatialOmega a xi = -spatialOmega a xi / (2 * Real.pi) := by ring
    have plus : -((-1) / (2 * Real.pi)) * spatialOmega a xi = spatialOmega a xi / (2 * Real.pi) := by ring
    rw [minus, plus]
    simp only [← mul_assoc]
    rw [show spatialFourierKernel x xi * temporalFourierKernel (-spatialOmega a xi / (2 * Real.pi)) t *
        (((spatialOmega a xi)⁻¹ : ℝ) : ℂ) * G xi -
        spatialFourierKernel x xi * temporalFourierKernel (spatialOmega a xi / (2 * Real.pi)) t *
          (((spatialOmega a xi)⁻¹ : ℝ) : ℂ) * G xi =
        spatialFourierKernel x xi *
          (temporalFourierKernel (-spatialOmega a xi / (2 * Real.pi)) t -
           temporalFourierKernel (spatialOmega a xi / (2 * Real.pi)) t) *
          (((spatialOmega a xi)⁻¹ : ℝ) : ℂ) * G xi by ring]
    rw [temporalFourierKernel_shell_difference]
    simp only [spatialSineCoefficient, sineCauchyCoefficient, temporalShellSine, spatialOmega]
    push_cast
    field_simp
    <;> ring

theorem full_flat_joint_smooth (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × KGSpatialSpace => fullFlatPosition a f h z.1 z.2) := by
  have cosine := (homogeneous_phase_smooth a 1 (𝓕 f)).add
    (homogeneous_phase_smooth a (-1) (𝓕 f))
  have sine := (homogeneous_phase_smooth a 1 (spatialInverseOmegaMultiplierCLM a (𝓕 h))).sub
    (homogeneous_phase_smooth a (-1) (spatialInverseOmegaMultiplierCLM a (𝓕 h)))
  have combined : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × KGSpatialSpace =>
      (1 / 2 : ℂ) *
        (volumePhaseIntegral (homogeneousPhaseFrequency a 1) (𝓕 f) (spacetimeSpatialJoin z) +
         volumePhaseIntegral (homogeneousPhaseFrequency a (-1)) (𝓕 f) (spacetimeSpatialJoin z)) +
      (2 * Complex.I)⁻¹ *
        (volumePhaseIntegral (homogeneousPhaseFrequency a 1) (spatialInverseOmegaMultiplierCLM a (𝓕 h))
          (spacetimeSpatialJoin z) -
         volumePhaseIntegral (homogeneousPhaseFrequency a (-1)) (spatialInverseOmegaMultiplierCLM a (𝓕 h))
          (spacetimeSpatialJoin z))) :=
    (contDiff_const.mul (cosine.comp spacetimeSpatialJoin.contDiff)).add
      (contDiff_const.mul (sine.comp spacetimeSpatialJoin.contDiff))
  convert combined using 1
  funext z
  change spatialCosineSolutionCLM a z.1 f z.2 + spatialSineSolutionCLM a z.1 h z.2 = _
  rw [cosine_phase_average, sine_phase_difference]
  rfl

end AASCKleinGordon.CurvedKG
