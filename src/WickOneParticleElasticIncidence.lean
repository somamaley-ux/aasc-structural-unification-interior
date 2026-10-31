import WickOneParticleChannels
import WickPhysicalMeasureSplit
import KGOneParticleCoreEmbedding

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
open MeasureTheory
open scoped BigOperators SchwartzMap FourierTransform
namespace AASCKleinGordon

/-- Fixed original Fourier convention, bra p and ket q. -/
def wickElasticPhase (a : Parameters) (x : Spacetime) (p q : Momentum) : ℂ :=
  Real.fourierChar (-inner ℝ x (shellFrequency a p-shellFrequency a q))

def wickOneParticleElasticIntegrand (a : Parameters) (f g : bosonicSchwartz 1)
    (i j : Fin 4) (x : Spacetime) (z : ParticleConfiguration 2) : ℂ :=
  wickElasticPhase a x (z 0) (z 1)*
    (scalarMatrixElement a (massShell a (z 0)) (massShell a (z 1)) i j : ℂ)*
      star (sectorOneToSchwartz f (z 0))*sectorOneToSchwartz g (z 1)

theorem wick_one_particle_mixed_state_apply (f g : bosonicSchwartz 1) (z : ParticleConfiguration 2) :
    wickCoreChannelStateKernel 0 (wickOneParticleCore f) (wickOneParticleCore g) 1 z=
      star (sectorOneToSchwartz f (z 0))*sectorOneToSchwartz g (z 1) := by
  change wickMixedStateKernel 0 (wickOneParticleCore f 1).val (wickOneParticleCore g 1).val z=_
  rw [wick_one_particle_at_sector,wick_one_particle_at_sector,wickMixedStateKernel_apply]
  have h0 : Fin.cons (z 0) (Fin.tail (Fin.tail z))=oneConfigurationEquiv.symm (z 0) := by
    ext k; fin_cases k; rfl
  have h1 : Fin.tail z=oneConfigurationEquiv.symm (z 1) := by
    ext k; fin_cases k; rfl
  rw [h0,h1]
  rfl

theorem wick_one_particle_elastic_integrand_is_actual (a : Parameters) (f g : bosonicSchwartz 1)
    (i j : Fin 4) (x : Spacetime) (z : ParticleConfiguration 2) :
    wickOneParticleElasticIntegrand a f g i j x z=
      (2*(a.hbar : ℂ)^2)*
        (Real.fourierChar (-inner ℝ x (wickCoreChannelFrequency0 a 0 1 z+
          wickCoreChannelFrequency1 a 0 1 z)) •
            wickRaisedStressKernel a 2 (wickCoreChannelFrequency0 a 0 1)
              (wickCoreChannelFrequency1 a 0 1)
              (wickCoreChannelStateKernel 0 (wickOneParticleCore f) (wickOneParticleCore g) 1) i j z) := by
  have h := wick_actual_CA_kernel_elastic_tensor a 0
    (wickCoreChannelStateKernel 0 (wickOneParticleCore f) (wickOneParticleCore g) 1) z i j
  rw [wick_one_particle_mixed_state_apply] at h
  change _=(2*(a.hbar : ℂ)^2)*(wickElasticPhase a x (z 0) (z 1)*_)
  dsimp only [wickOneParticleElasticIntegrand]
  linear_combination -(wickElasticPhase a x (z 0) (z 1))*h

theorem wick_one_particle_elastic_integrand_integrable (a : Parameters) (f g : bosonicSchwartz 1)
    (i j : Fin 4) (x : Spacetime) :
    Integrable (wickOneParticleElasticIntegrand a f g i j x) (particleMeasure a 2) := by
  change Integrable (fun z : ParticleConfiguration 2 => wickOneParticleElasticIntegrand a f g i j x z)
    (particleMeasure a 2)
  simp_rw [wick_one_particle_elastic_integrand_is_actual]
  exact (wickLocalMatrix_integrable a 2 _
    ((wickCoreChannelFrequency0_temperate a 0 1).add
      (wickCoreChannelFrequency1_temperate a 0 1)).1.continuous _ x).const_mul _

theorem wick_one_particle_elastic_integral_actual_matrix (a : Parameters) (f g : bosonicSchwartz 1)
    (i j : Fin 4) (x : Spacetime) :
    (∫ z,wickOneParticleElasticIntegrand a f g i j x z ∂particleMeasure a 2)=
      2*(a.hbar : ℂ)^2*
        wickCoreRaisedStressMatrix a 0 (wickOneParticleCore f) (wickOneParticleCore g) 1 i j x := by
  simp_rw [wick_one_particle_elastic_integrand_is_actual]
  rw [integral_const_mul]
  rfl

theorem wick_one_particle_elastic_double_integral (a : Parameters) (f g : bosonicSchwartz 1)
    (i j : Fin 4) (x : Spacetime) :
    (∫ z,wickOneParticleElasticIntegrand a f g i j x z ∂particleMeasure a 2)=
      ∫ p,∫ q,wickElasticPhase a x p q*
        (scalarMatrixElement a (massShell a p) (massShell a q) i j : ℂ)*
          star (sectorOneToSchwartz f p)*sectorOneToSchwartz g q
            ∂wignerMeasure a ∂wignerMeasure a := by
  rw [wick_particle_integral_two_visible a 0 _
    (wick_one_particle_elastic_integrand_integrable a f g i j x)]
  apply integral_congr_ae
  exact ae_of_all _ fun p => by
    apply integral_congr_ae
    exact ae_of_all _ fun q => by
      simp [wickOneParticleElasticIntegrand,integral_unique,particleMeasure,Measure.real]

/-- The original action tensor specialized to arbitrary original one-particle
states; both original Wigner measures and the exact amplitude remain visible. -/
theorem wick_original_one_particle_elastic_incidence (a : Parameters) (s : ℝ)
    (f g : bosonicSchwartz 1) (i j : Fin 4) (x : Spacetime) :
    originalWickScalarStressRaisedMatrix a s (wickOneParticleCore f) (wickOneParticleCore g) i j x=
      ((s : ℂ)^2/(a.hbar : ℂ)^2)*
        ∫ p,∫ q,wickElasticPhase a x p q*
          (scalarMatrixElement a (massShell a p) (massShell a q) i j : ℂ)*
            star (sectorOneToSchwartz f p)*sectorOneToSchwartz g q
              ∂wignerMeasure a ∂wignerMeasure a := by
  rw [← wick_one_particle_elastic_double_integral,wick_one_particle_elastic_integral_actual_matrix,
    wick_original_one_particle_stress_two_mixed]
  have hh : (a.hbar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr a.hbar_pos.ne'
  field_simp [hh]

/-- Both Wigner weights occur in the ordinary-volume form of the same tensor. -/
theorem wick_original_one_particle_elastic_weighted_volume (a : Parameters) (s : ℝ)
    (f g : bosonicSchwartz 1) (i j : Fin 4) (x : Spacetime) :
    originalWickScalarStressRaisedMatrix a s (wickOneParticleCore f) (wickOneParticleCore g) i j x=
      ((s : ℂ)^2/(a.hbar : ℂ)^2)*
        ∫ p,∫ q,(wignerWeight a p : ℂ)*(wignerWeight a q : ℂ)*
          (wickElasticPhase a x p q*
            (scalarMatrixElement a (massShell a p) (massShell a q) i j : ℂ)*
              star (sectorOneToSchwartz f p)*sectorOneToSchwartz g q) := by
  rw [wick_original_one_particle_elastic_incidence,wick_two_wigner_integrals_weighted_volume]

end AASCKleinGordon
