import WickStressChargeGeneratorCalibration
import WickOriginalEventSign

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace AASCKleinGordon

theorem wick_positive_calibrated_energy_charge_eq_original (a : Parameters) :
    wickOriginalStressEnergyCharge a (wickPositiveCalibratedAmplitude a)=fockCoreEnergy a := by
  apply LinearPMap.ext (f := wickOriginalStressEnergyCharge a (wickPositiveCalibratedAmplitude a))
    (g := fockCoreEnergy a) rfl
  intro x hx hy
  let f : fockCoreDomain a := ⟨x,hx⟩
  let v := (fockCoreDomainEquiv a).symm f
  have hf : includedFockCore a v=f := (fockCoreDomainEquiv a).apply_symm_apply f
  change wickOriginalStressEnergyCharge a (wickPositiveCalibratedAmplitude a) f=fockCoreEnergy a f
  have actual := wick_original_stress_energy_on_core a (wickPositiveCalibratedAmplitude a) v
  rw [hf,wick_positive_calibrated_amplitude_coefficient,one_smul] at actual
  have original := fockCoreEnergy_on_original_core a v
  rw [hf] at original
  exact actual.trans original.symm

theorem wick_positive_calibrated_spatial_charge_eq_original (a : Parameters) (j : Fin 3) :
    wickOriginalStressCharge a (wickPositiveCalibratedAmplitude a) j.succ=fockCoreSpatialCharge a j := by
  apply LinearPMap.ext (f := wickOriginalStressCharge a (wickPositiveCalibratedAmplitude a) j.succ)
    (g := fockCoreSpatialCharge a j) rfl
  intro x hx hy
  let f : fockCoreDomain a := ⟨x,hx⟩
  let v := (fockCoreDomainEquiv a).symm f
  have hf : includedFockCore a v=f := (fockCoreDomainEquiv a).apply_symm_apply f
  change wickOriginalStressCharge a (wickPositiveCalibratedAmplitude a) j.succ f=fockCoreSpatialCharge a j f
  have actual := wick_original_stress_spatial_on_core a (wickPositiveCalibratedAmplitude a) j v
  rw [hf,wick_positive_calibrated_amplitude_coefficient,one_smul] at actual
  have original := fockCoreSpatialCharge_on_original_core a j v
  rw [hf] at original
  exact actual.trans original.symm

theorem wick_positive_calibrated_energy_closure_maximal (a : Parameters) :
    (wickOriginalStressEnergyCharge a (wickPositiveCalibratedAmplitude a)).closure=fockMaximalEnergy a := by
  rw [wick_positive_calibrated_energy_charge_eq_original,fockCoreEnergy_closure_eq_maximal]

theorem wick_positive_calibrated_spatial_closure_maximal (a : Parameters) (j : Fin 3) :
    (wickOriginalStressCharge a (wickPositiveCalibratedAmplitude a) j.succ).closure=
      fockMaximalSpatialMomentum a j := by
  rw [wick_positive_calibrated_spatial_charge_eq_original,fockCoreSpatialCharge_closure_eq_maximal]

theorem wick_positive_calibrated_energy_closure_exact_generator (a : Parameters) :
    GlobalCharge.ExactGenerator (Translation.coefficient a.hbar) (fockTimeTranslation a)
      (wickOriginalStressEnergyCharge a (wickPositiveCalibratedAmplitude a)).closure := by
  rw [wick_positive_calibrated_energy_charge_eq_original]
  exact fockTimeTranslation_originalClosure_exactGenerator a

theorem wick_positive_calibrated_spatial_closure_exact_generator (a : Parameters) (j : Fin 3) :
    GlobalCharge.ExactGenerator (Translation.coefficient a.hbar) (fockSpatialTranslation a j)
      (wickOriginalStressCharge a (wickPositiveCalibratedAmplitude a) j.succ).closure := by
  rw [wick_positive_calibrated_spatial_charge_eq_original]
  exact fockSpatialTranslation_originalClosure_exactGenerator a j

theorem wick_original_four_momentum_vacuum_zero (a : Parameters) (j : Fin 4) :
    wickOriginalCoreFourMomentum a j vacuumCore=0 := by
  cases j using Fin.cases with
  | zero => simp [wick_original_core_four_momentum_time,wick_original_core_energy_vacuum_zero]
  | succ j => exact coreSpatialMomentum_vacuum_zero j

theorem wick_original_stress_charge_vacuum_zero (a : Parameters) (s : ℝ) (j : Fin 4) :
    wickOriginalStressCharge a s j (includedFockCore a vacuumCore)=0 := by
  rw [wick_original_stress_charge_on_core]
  change finiteParticleCoreToFock a (wickSameTensorChargeCoefficient a s •
    wickOriginalCoreFourMomentum a j vacuumCore)=0
  rw [wick_original_four_momentum_vacuum_zero,smul_zero,map_zero]

theorem wick_original_hypersurface_vacuum_baseline (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (j : Fin 4) (τ : ℝ) :
    wickOriginalHypersurfaceCharge a s u vacuumCore j τ=0 := by
  rw [← wick_original_stress_charge_hypersurface_pairing,
    wick_original_stress_charge_vacuum_zero,inner_zero_right]

end AASCKleinGordon
