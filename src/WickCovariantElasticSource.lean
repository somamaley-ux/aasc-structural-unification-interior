import WickCovariantRigging

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

def wickCovariantTensorKernel (a : Parameters) (s : ℝ) (p q : Momentum) (i j : Fin 4) : ℂ :=
  ((wickCovariantScale a : ℂ)*(s : ℂ)^2/(a.hbar : ℂ)^2)*
    (scalarMatrixElement a (massShell a p) (massShell a q) i j : ℂ)

theorem wick_covariant_wavefunction_pair (a : Parameters) (f g : 𝓢(Momentum,ℂ)) (p q : Momentum) :
    star (wickCovariantSchwartz a f p)*wickCovariantSchwartz a g q=
      (wickCovariantScale a : ℂ)*(star (f p)*g q) := by
  simp only [wickCovariantSchwartz,SchwartzMap.smul_apply,smul_eq_mul,star_mul]
  rw [show star (wickCovariantRoot a : ℂ)=(wickCovariantRoot a : ℂ) from Complex.conj_ofReal _]
  have hsq : (wickCovariantRoot a : ℂ)^2=(wickCovariantScale a : ℂ) := by
    exact_mod_cast wick_covariant_root_sq a
  linear_combination (star (f p)*g q)*hsq

/-- Transport of both measures and both state factors; exactly one net K remains. -/
theorem wick_covariant_double_pairing_transport (a : Parameters) (s : ℝ)
    (F : Momentum → Momentum → ℂ) (f g : 𝓢(Momentum,ℂ)) :
    ((s : ℂ)^2/(a.hbar : ℂ)^2)*
      (∫ p,∫ q,F p q*star (f p)*g q ∂wignerMeasure a ∂wignerMeasure a)=
        ∫ p,∫ q,((wickCovariantScale a : ℂ)*(s : ℂ)^2/(a.hbar : ℂ)^2)*
          F p q*star (wickCovariantSchwartz a f p)*wickCovariantSchwartz a g q
            ∂wickCovariantMeasure a ∂wickCovariantMeasure a := by
  rw [wick_wigner_double_integral_covariant]
  calc
    _ = ∫ p,∫ q,(((s : ℂ)^2/(a.hbar : ℂ)^2)*(wickCovariantScale a : ℂ)^2)*
        (F p q*star (f p)*g q) ∂wickCovariantMeasure a ∂wickCovariantMeasure a := by
      simp_rw [integral_const_mul]
      ring
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun p => by
        apply integral_congr_ae
        exact ae_of_all _ fun q => by
          have h := wick_covariant_wavefunction_pair a f g p q
          calc
            _ = ((wickCovariantScale a : ℂ)*(s : ℂ)^2/(a.hbar : ℂ)^2)*
                F p q*((wickCovariantScale a : ℂ)*(star (f p)*g q)) := by ring
            _ = _ := by rw [← h];ring

theorem wick_original_covariant_tensor_incidence (a : Parameters) (s : ℝ)
    (f g : bosonicSchwartz 1) (i j : Fin 4) (x : Spacetime) :
    originalWickScalarStressRaisedMatrix a s (wickOneParticleCore f) (wickOneParticleCore g) i j x=
      ∫ p,∫ q,wickElasticPhase a x p q*wickCovariantTensorKernel a s p q i j*
        star (wickCovariantSchwartz a (sectorOneToSchwartz f) p)*
          wickCovariantSchwartz a (sectorOneToSchwartz g) q
            ∂wickCovariantMeasure a ∂wickCovariantMeasure a := by
  rw [wick_original_one_particle_elastic_incidence,
    wick_covariant_double_pairing_transport a s
      (fun p q => wickElasticPhase a x p q*
        (scalarMatrixElement a (massShell a p) (massShell a q) i j : ℂ))]
  apply integral_congr_ae
  exact ae_of_all _ fun p => by
    apply integral_congr_ae
    exact ae_of_all _ fun q => by unfold wickCovariantTensorKernel;ring

theorem wick_original_covariant_source_test_incidence (a : Parameters) (s : ℝ)
    (f g : bosonicSchwartz 1) (i j : Fin 4) (h : 𝓢(Spacetime,ℂ)) :
    originalWickRaisedStressDistribution a s (wickOneParticleCore f) (wickOneParticleCore g) i j h=
      ∫ p,∫ q,(𝓕 h) (shellFrequency a p-shellFrequency a q)*wickCovariantTensorKernel a s p q i j*
        star (wickCovariantSchwartz a (sectorOneToSchwartz f) p)*
          wickCovariantSchwartz a (sectorOneToSchwartz g) q
            ∂wickCovariantMeasure a ∂wickCovariantMeasure a := by
  rw [wick_original_one_particle_source_double_test_incidence]
  refine (wick_covariant_double_pairing_transport a s
    (fun (p q : Momentum) => (𝓕 h : 𝓢(Spacetime,ℂ)) (shellFrequency a p-shellFrequency a q)*
      (scalarMatrixElement a (massShell a p) (massShell a q) i j : ℂ))
    (sectorOneToSchwartz f) (sectorOneToSchwartz g)).trans ?_
  apply integral_congr_ae
  exact ae_of_all _ fun p => by
    apply integral_congr_ae
    exact ae_of_all _ fun q => by unfold wickCovariantTensorKernel;ring

theorem wick_covariant_calibrated_tensor_kernel (a : Parameters) (p q : Momentum) (i j : Fin 4) :
    wickCovariantTensorKernel a (wickPositiveCalibratedAmplitude a) p q i j=
      (a.speed : ℂ)*(scalarMatrixElement a (massShell a p) (massShell a q) i j : ℂ) := by
  have h : (wickCovariantScale a : ℂ)*(wickPositiveCalibratedAmplitude a : ℂ)^2/(a.hbar : ℂ)^2=
      (a.speed : ℂ) := by
    exact_mod_cast (show wickCovariantScale a*(wickPositiveCalibratedAmplitude a)^2/a.hbar^2=a.speed by
      simpa only [wickCovariantScale] using wick_calibrated_covariant_measure_coefficient a)
  rw [wickCovariantTensorKernel,h]

def wickPositiveElasticPhase (a : Parameters) (x : Spacetime) (p q : Momentum) : ℂ :=
  Real.fourierChar (inner ℝ x (shellFrequency a p-shellFrequency a q))

theorem wick_elastic_phase_passive_event (a : Parameters) (x : Spacetime) (p q : Momentum) :
    wickElasticPhase a (-x) p q=wickPositiveElasticPhase a x p q := by
  simp [wickElasticPhase,wickPositiveElasticPhase,inner_neg_left]

/-- Explicit event negation; this is not an assumed corpus role identification. -/
theorem wick_original_covariant_passive_event_incidence (a : Parameters) (s : ℝ)
    (f g : bosonicSchwartz 1) (i j : Fin 4) (x : Spacetime) :
    originalWickScalarStressRaisedMatrix a s (wickOneParticleCore f) (wickOneParticleCore g) i j (-x)=
      ∫ p,∫ q,wickPositiveElasticPhase a x p q*wickCovariantTensorKernel a s p q i j*
        star (wickCovariantSchwartz a (sectorOneToSchwartz f) p)*
          wickCovariantSchwartz a (sectorOneToSchwartz g) q
            ∂wickCovariantMeasure a ∂wickCovariantMeasure a := by
  rw [wick_original_covariant_tensor_incidence]
  simp_rw [wick_elastic_phase_passive_event]

end AASCKleinGordon
