import WickOneParticleElasticIncidence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
open MeasureTheory
open scoped BigOperators SchwartzMap FourierTransform
namespace AASCKleinGordon

def wickOneParticleElasticTestIntegrand (a : Parameters) (f g : bosonicSchwartz 1)
    (i j : Fin 4) (h : 𝓢(Spacetime,ℂ)) (z : ParticleConfiguration 2) : ℂ :=
  (𝓕 h) (shellFrequency a (z 0)-shellFrequency a (z 1))*
    (scalarMatrixElement a (massShell a (z 0)) (massShell a (z 1)) i j : ℂ)*
      star (sectorOneToSchwartz f (z 0))*sectorOneToSchwartz g (z 1)

theorem wick_one_particle_elastic_test_integrand_is_actual (a : Parameters) (f g : bosonicSchwartz 1)
    (i j : Fin 4) (h : 𝓢(Spacetime,ℂ)) (z : ParticleConfiguration 2) :
    wickOneParticleElasticTestIntegrand a f g i j h z=
      (2*(a.hbar : ℂ)^2)*
        ((𝓕 h) (wickCoreChannelFrequency0 a 0 1 z+wickCoreChannelFrequency1 a 0 1 z)*
            wickRaisedStressKernel a 2 (wickCoreChannelFrequency0 a 0 1)
              (wickCoreChannelFrequency1 a 0 1)
              (wickCoreChannelStateKernel 0 (wickOneParticleCore f) (wickOneParticleCore g) 1) i j z) := by
  have heq := wick_actual_CA_kernel_elastic_tensor a 0
    (wickCoreChannelStateKernel 0 (wickOneParticleCore f) (wickOneParticleCore g) 1) z i j
  rw [wick_one_particle_mixed_state_apply] at heq
  change _=(2*(a.hbar : ℂ)^2)*((𝓕 h) (shellFrequency a (z 0)-shellFrequency a (z 1))*_)
  dsimp only [wickOneParticleElasticTestIntegrand]
  linear_combination -((𝓕 h) (shellFrequency a (z 0)-shellFrequency a (z 1)))*heq

theorem wick_one_particle_elastic_test_integrable (a : Parameters) (f g : bosonicSchwartz 1)
    (i j : Fin 4) (h : 𝓢(Spacetime,ℂ)) :
    Integrable (wickOneParticleElasticTestIntegrand a f g i j h) (particleMeasure a 2) := by
  change Integrable (fun z : ParticleConfiguration 2 => wickOneParticleElasticTestIntegrand a f g i j h z)
    (particleMeasure a 2)
  simp_rw [wick_one_particle_elastic_test_integrand_is_actual]
  exact (wickKernelTest_integrable a 2 _
    ((wickCoreChannelFrequency0_temperate a 0 1).add
      (wickCoreChannelFrequency1_temperate a 0 1)).1.continuous _ (𝓕 h)).const_mul _

theorem wick_one_particle_elastic_test_integral_actual (a : Parameters) (f g : bosonicSchwartz 1)
    (i j : Fin 4) (h : 𝓢(Spacetime,ℂ)) :
    (∫ z,wickOneParticleElasticTestIntegrand a f g i j h z ∂particleMeasure a 2)=
      2*(a.hbar : ℂ)^2 * wickKernelEvaluationCLM a 2
        (fun z => wickCoreChannelFrequency0 a 0 1 z+wickCoreChannelFrequency1 a 0 1 z)
        ((wickCoreChannelFrequency0_temperate a 0 1).add
          (wickCoreChannelFrequency1_temperate a 0 1)).1.continuous
        (wickRaisedStressKernel a 2 (wickCoreChannelFrequency0 a 0 1)
          (wickCoreChannelFrequency1 a 0 1)
          (wickCoreChannelStateKernel 0 (wickOneParticleCore f) (wickOneParticleCore g) 1) i j) (𝓕 h) := by
  simp_rw [wick_one_particle_elastic_test_integrand_is_actual]
  rw [integral_const_mul]
  rfl

/-- Same-source offdiagonal distributional incidence. Absolute Fubini is
inherited from the actual Schwartz channel's proved local test pairing. -/
theorem wick_original_one_particle_source_test_incidence (a : Parameters) (s : ℝ)
    (f g : bosonicSchwartz 1) (i j : Fin 4) (h : 𝓢(Spacetime,ℂ)) :
    originalWickRaisedStressDistribution a s (wickOneParticleCore f) (wickOneParticleCore g) i j h=
      ((s : ℂ)^2/(a.hbar : ℂ)^2)*
        ∫ z,wickOneParticleElasticTestIntegrand a f g i j h z ∂particleMeasure a 2 := by
  rw [original_wick_raised_stress_distribution_pairing]
  have hp (x : Spacetime) :
      h x*originalWickScalarStressRaisedMatrix a s (wickOneParticleCore f) (wickOneParticleCore g) i j x=
        (2*(s : ℂ)^2)*(h x*wickCoreRaisedStressMatrix a 0
          (wickOneParticleCore f) (wickOneParticleCore g) 1 i j x) := by
    rw [wick_original_one_particle_stress_two_mixed]
    ring
  simp_rw [hp]
  rw [integral_const_mul,wick_one_particle_elastic_test_integral_actual]
  change (2*(s : ℂ)^2)*(∫ x,h x*wickLocalMatrix a 2
    (fun z => wickCoreChannelFrequency0 a 0 1 z+wickCoreChannelFrequency1 a 0 1 z)
    (wickRaisedStressKernel a 2 (wickCoreChannelFrequency0 a 0 1) (wickCoreChannelFrequency1 a 0 1)
      (wickCoreChannelStateKernel 0 (wickOneParticleCore f) (wickOneParticleCore g) 1) i j) x)=_
  rw [wickLocalMatrix_test_pairing a 2
    (fun z : ParticleConfiguration 2 => wickCoreChannelFrequency0 a 0 1 z+wickCoreChannelFrequency1 a 0 1 z)
    ((wickCoreChannelFrequency0_temperate a 0 1).add
      (wickCoreChannelFrequency1_temperate a 0 1)).1.continuous]
  have hh : (a.hbar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr a.hbar_pos.ne'
  field_simp [hh]

theorem wick_original_one_particle_source_double_test_incidence (a : Parameters) (s : ℝ)
    (f g : bosonicSchwartz 1) (i j : Fin 4) (h : 𝓢(Spacetime,ℂ)) :
    originalWickRaisedStressDistribution a s (wickOneParticleCore f) (wickOneParticleCore g) i j h=
      ((s : ℂ)^2/(a.hbar : ℂ)^2)*
        ∫ p,∫ q,(𝓕 h) (shellFrequency a p-shellFrequency a q)*
          (scalarMatrixElement a (massShell a p) (massShell a q) i j : ℂ)*
            star (sectorOneToSchwartz f p)*sectorOneToSchwartz g q
              ∂wignerMeasure a ∂wignerMeasure a := by
  rw [wick_original_one_particle_source_test_incidence,wick_particle_integral_two_visible a 0 _
    (wick_one_particle_elastic_test_integrable a f g i j h)]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun p => by
    apply integral_congr_ae
    exact ae_of_all _ fun q => by
      simp [wickOneParticleElasticTestIntegrand,integral_unique,particleMeasure,Measure.real]

theorem wick_calibrated_one_particle_transition_source_incidence (a : Parameters)
    (f g : bosonicSchwartz 1) (i j : Fin 4) (h : 𝓢(Spacetime,ℂ)) :
    wickCalibratedTransitionSource a (wickOneParticleCore f) (wickOneParticleCore g) i j h=
      (((wickPositiveCalibratedAmplitude a : ℂ)^2)/(a.hbar : ℂ)^2)*
        ∫ p,∫ q,(𝓕 h) (shellFrequency a p-shellFrequency a q)*
          (scalarMatrixElement a (massShell a p) (massShell a q) i j : ℂ)*
            star (sectorOneToSchwartz f p)*sectorOneToSchwartz g q
              ∂wignerMeasure a ∂wignerMeasure a :=
  wick_original_one_particle_source_double_test_incidence a (wickPositiveCalibratedAmplitude a) f g i j h

/-- Algebraic coefficient relevant to a covariant measure convention. The
measure/state unitary and generalized-state normalization are still to be built. -/
theorem wick_calibrated_covariant_measure_coefficient (a : Parameters) :
    2*a.mass*a.speed*wickSpatialFourierJacobian a*(wickPositiveCalibratedAmplitude a)^2/a.hbar^2=a.speed := by
  have hc := wick_positive_calibrated_amplitude_coefficient a
  rw [wick_same_tensor_charge_coefficient_real,← Complex.ofReal_one,Complex.ofReal_inj] at hc
  dsimp only [wickChargeNormalization] at hc
  linear_combination a.speed*hc

end AASCKleinGordon
