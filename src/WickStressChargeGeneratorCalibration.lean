import WickOriginalChargeFockIdentification
import WickOriginalTranslationSlope
import WickChargeAmplitudeNormalization
import KGSpacetimeTranslationUnitary

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 200000
namespace AASCKleinGordon

/-- Q^0 uses 1/c in the hypersurface integral; physical energy is c Q^0. -/
def wickOriginalStressEnergyCharge (a : Parameters) (s : ℝ) :
    FockHilbert a →ₗ.[ℂ] FockHilbert a :=
  (a.speed : ℂ) • wickOriginalStressCharge a s 0

theorem wick_original_stress_energy_on_core (a : Parameters) (s : ℝ)
    (v : FiniteParticleCore) :
    wickOriginalStressEnergyCharge a s (includedFockCore a v)=
      wickSameTensorChargeCoefficient a s • finiteParticleCoreToFock a (coreEnergy a v) := by
  change (a.speed : ℂ) • wickOriginalStressCharge a s 0 (includedFockCore a v)=_
  rw [wick_original_stress_charge_on_core]
  change (a.speed : ℂ) • finiteParticleCoreToFock a
    (wickSameTensorChargeCoefficient a s • ((a.speed : ℂ)⁻¹ • coreEnergy a v))=_
  simp only [map_smul,smul_smul]
  congr 1
  have hc : (a.speed : ℂ)≠0 := Complex.ofReal_ne_zero.mpr a.speed_pos.ne'
  field_simp

theorem wick_original_stress_spatial_on_core (a : Parameters) (s : ℝ) (j : Fin 3)
    (v : FiniteParticleCore) :
    wickOriginalStressCharge a s j.succ (includedFockCore a v)=
      wickSameTensorChargeCoefficient a s • finiteParticleCoreToFock a (coreSpatialMomentum j v) := by
  rw [wick_original_stress_charge_on_core]
  change finiteParticleCoreToFock a (wickSameTensorChargeCoefficient a s • coreSpatialMomentum j v)=_
  exact map_smul _ _ _

/-- Calibration follows AFTER identifying the actual integrated tensor
charge with its original Fock operator. It is not a premise of that identity. -/
theorem wick_original_stress_energy_generator_calibration_iff (a : Parameters) (s : ℝ) :
    (∀ v : FiniteParticleCore,
      HasDerivAt (fun t => fockTimeTranslation a t (finiteParticleCoreToFock a v))
        (Translation.coefficient a.hbar •
          wickOriginalStressEnergyCharge a s (includedFockCore a v)) 0) ↔
      s^2=1/wickChargeNormalization a := by
  simp_rw [wick_original_stress_energy_on_core]
  rw [wick_original_time_translation_scaled_slope_iff,
    wick_same_tensor_charge_coefficient_one_iff]

theorem wick_original_positive_calibrated_energy_generator (a : Parameters)
    (v : FiniteParticleCore) :
    HasDerivAt (fun t => fockTimeTranslation a t (finiteParticleCoreToFock a v))
      (Translation.coefficient a.hbar •
        wickOriginalStressEnergyCharge a (wickPositiveCalibratedAmplitude a) (includedFockCore a v)) 0 := by
  rw [wick_original_stress_energy_on_core,wick_positive_calibrated_amplitude_coefficient,one_smul]
  exact wick_original_time_translation_core_derivative a v

theorem wick_original_positive_calibrated_spatial_generator (a : Parameters) (j : Fin 3)
    (v : FiniteParticleCore) :
    HasDerivAt (fun t => fockSpatialTranslation a j t (finiteParticleCoreToFock a v))
      (Translation.coefficient a.hbar •
        wickOriginalStressCharge a (wickPositiveCalibratedAmplitude a) j.succ (includedFockCore a v)) 0 := by
  rw [wick_original_stress_spatial_on_core,wick_positive_calibrated_amplitude_coefficient,one_smul]
  exact wick_original_spatial_translation_core_derivative a j v

theorem wick_original_zero_amplitude_fails_generator_matching (a : Parameters) :
    ¬ (∀ v : FiniteParticleCore,
      HasDerivAt (fun t => fockTimeTranslation a t (finiteParticleCoreToFock a v))
        (Translation.coefficient a.hbar •
          wickOriginalStressEnergyCharge a 0 (includedFockCore a v)) 0) := by
  intro h
  have hc := (wick_original_stress_energy_generator_calibration_iff a 0).mp h
  norm_num at hc
  exact (wick_charge_normalization_positive a).ne' hc.symm

end AASCKleinGordon
