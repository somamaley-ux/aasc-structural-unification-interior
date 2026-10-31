import KGNativeWickRaySource

noncomputable section
set_option maxHeartbeats 8000000
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

def originalWickUnitRepresentative (a : Parameters) (u : FiniteParticleCore) : FiniteParticleCore :=
  ((‖finiteParticleCoreToFock a u‖⁻¹ : ℝ) : ℂ) • u

theorem original_wick_core_embedding_norm_positive (a : Parameters) (u : FiniteParticleCore) (hu : u≠0) :
    0<‖finiteParticleCoreToFock a u‖ := by
  apply norm_pos_iff.mpr
  intro hz
  exact hu ((finiteParticleCoreToFock_injective a) (by simpa using hz))

theorem original_wick_unit_representative_norm (a : Parameters) (u : FiniteParticleCore) (hu : u≠0) :
    ‖finiteParticleCoreToFock a (originalWickUnitRepresentative a u)‖=1 := by
  have hn := original_wick_core_embedding_norm_positive a u hu
  have hc : ‖((‖finiteParticleCoreToFock a u‖⁻¹ : ℝ) : ℂ)‖=‖finiteParticleCoreToFock a u‖⁻¹ := by
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_of_pos hn]
  rw [originalWickUnitRepresentative,map_smul,norm_smul,hc,inv_mul_cancel₀ hn.ne']

def originalWickUnitNonzeroRepresentative (a : Parameters) (u : WickNonzeroCore) : WickNonzeroCore :=
  ⟨originalWickUnitRepresentative a u.val,by
    intro hz
    have hn := original_wick_unit_representative_norm a u.val u.property
    rw [hz,map_zero,norm_zero] at hn
    norm_num at hn⟩

theorem original_wick_unit_representative_same_ray (a : Parameters) (u : WickNonzeroCore) :
    Quotient.mk wickCoreRaySetoid (originalWickUnitNonzeroRepresentative a u)=
      Quotient.mk wickCoreRaySetoid u := by
  apply Eq.symm
  apply Quotient.sound
  refine ⟨((‖finiteParticleCoreToFock a u.val‖⁻¹ : ℝ) : ℂ),?_,rfl⟩
  exact_mod_cast inv_ne_zero (original_wick_core_embedding_norm_positive a u.val u.property).ne'

theorem original_wick_ray_source_is_actual_unit_response (a : Parameters) (s : ℝ)
    (Ω : Opens (Fin 4 → ℝ)) (u : WickNonzeroCore) :
    originalWickRayMetricResponse a s Ω (Quotient.mk wickCoreRaySetoid u)=
      originalWickNativeRealMetricResponse a s (originalWickUnitRepresentative a u.val) Ω := by
  rw [← original_wick_unit_representative_same_ray a u]
  exact original_wick_ray_source_on_unit_representative a s Ω
    (originalWickUnitNonzeroRepresentative a u)
    (original_wick_unit_representative_norm a u.val u.property)

theorem original_wick_core_norm_sq_continuous (a : Parameters) :
    Continuous (originalWickCoreNormSq a) :=
  (finiteParticleCoreToFock_continuous a).norm.pow 2

theorem original_wick_unit_representative_core_continuous (a : Parameters) :
    Continuous (fun u : WickNonzeroCore => originalWickUnitRepresentative a u.val) := by
  have hn : Continuous (fun u : WickNonzeroCore => ‖finiteParticleCoreToFock a u.val‖) :=
    ((finiteParticleCoreToFock_continuous a).comp continuous_subtype_val).norm
  exact (Complex.continuous_ofReal.comp (hn.inv₀ (fun u =>
    (original_wick_core_embedding_norm_positive a u.val u.property).ne'))).smul continuous_subtype_val

end AASCKleinGordon
