import WickOriginalEnergyActivity

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
namespace AASCKleinGordon

theorem wick_original_time_translation_core_derivative (a : Parameters) (v : FiniteParticleCore) :
    HasDerivAt (fun t => fockTimeTranslation a t (finiteParticleCoreToFock a v))
      (Translation.coefficient a.hbar • finiteParticleCoreToFock a (coreEnergy a v)) 0 := by
  obtain ⟨w,hw,he⟩ := (LinearPMap.mem_graph_iff _).mp
    (fockMaximalEnergy_graph_on_original_core a v)
  have derivative := (fockTimeTranslation_exactGenerator a).2 w
  simpa only [hw,he] using derivative

theorem wick_original_spatial_translation_core_derivative (a : Parameters) (j : Fin 3)
    (v : FiniteParticleCore) :
    HasDerivAt (fun t => fockSpatialTranslation a j t (finiteParticleCoreToFock a v))
      (Translation.coefficient a.hbar • finiteParticleCoreToFock a (coreSpatialMomentum j v)) 0 := by
  obtain ⟨w,hw,he⟩ := (LinearPMap.mem_graph_iff _).mp
    (fockMaximalSpatialMomentum_graph_on_original_core a j v)
  have derivative := (fockSpatialTranslation_exactGenerator a j).2 w
  simpa only [hw,he] using derivative

/-- Equality with the original time-translation slope determines the scale
on the actual occupied core. The vacuum baseline alone cannot do so. -/
theorem wick_original_time_translation_scaled_slope_iff (a : Parameters) (z : ℂ) :
    (∀ v : FiniteParticleCore,
      HasDerivAt (fun t => fockTimeTranslation a t (finiteParticleCoreToFock a v))
        (Translation.coefficient a.hbar • (z • finiteParticleCoreToFock a (coreEnergy a v))) 0) ↔
      z=1 := by
  constructor
  · intro derivative
    apply (wick_original_fock_energy_scale_equality_iff a z).mp
    intro v
    exact (smul_right_injective (FockHilbert a)
      (GlobalCharge.physical_generator_coefficient_nonzero a.hbar a.hbar_pos))
        ((derivative v).unique (wick_original_time_translation_core_derivative a v))
  · rintro rfl
    intro v
    simpa only [one_smul] using wick_original_time_translation_core_derivative a v

end AASCKleinGordon
