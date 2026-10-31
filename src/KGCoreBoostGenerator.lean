import KGOriginalCoreBoostDerivative
import UnitaryGroupDifferential

noncomputable section
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory
open scoped SchwartzMap Topology
namespace AASCKleinGordon
theorem coreAxisBoostDifferential_skew (a : Parameters) (u v : FiniteParticleCore) :
    inner ℂ (finiteParticleCoreToFock a (coreAxisBoostDifferential a u)) (finiteParticleCoreToFock a v) +
      inner ℂ (finiteParticleCoreToFock a u) (finiteParticleCoreToFock a (coreAxisBoostDifferential a v)) = 0 := by
  exact UnitaryCore.orbit_tangents_skew (fockAxisBoostUnitary a) (fockAxisBoostUnitary_zero a)
    (finiteParticleCoreToFock a u) (finiteParticleCoreToFock a v)
    (finiteParticleCoreToFock a (coreAxisBoostDifferential a u))
    (finiteParticleCoreToFock a (coreAxisBoostDifferential a v))
    (fockAxisBoost_original_core_hasDerivAt_zero a u) (fockAxisBoost_original_core_hasDerivAt_zero a v)


def axisBoostGeneratorScale (a : Parameters) : ℂ := -Complex.I*((a.hbar/a.speed : ℝ) : ℂ)

theorem axisBoostGeneratorScale_ne_zero (a : Parameters) : axisBoostGeneratorScale a ≠ 0 := by
  apply mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
  exact_mod_cast div_ne_zero a.hbar_pos.ne' a.speed_pos.ne'

theorem star_axisBoostGeneratorScale (a : Parameters) : star (axisBoostGeneratorScale a) = -axisBoostGeneratorScale a := by
  simp [axisBoostGeneratorScale,star_mul,mul_comm]

def coreAxisBoostGenerator (a : Parameters) : FiniteParticleCore →ₗ[ℂ] FiniteParticleCore :=
  axisBoostGeneratorScale a • coreAxisBoostDifferential a

theorem coreAxisBoostGenerator_inclusion (a : Parameters) (u : FiniteParticleCore) :
    finiteParticleCoreToFock a (coreAxisBoostGenerator a u) =
      axisBoostGeneratorScale a • finiteParticleCoreToFock a (coreAxisBoostDifferential a u) := by
  change finiteParticleCoreToFock a (axisBoostGeneratorScale a • coreAxisBoostDifferential a u) = _
  exact (finiteParticleCoreToFock a).map_smul (axisBoostGeneratorScale a) _

theorem coreAxisBoostGenerator_symmetric (a : Parameters) (u v : FiniteParticleCore) :
    inner ℂ (finiteParticleCoreToFock a (coreAxisBoostGenerator a u)) (finiteParticleCoreToFock a v) =
      inner ℂ (finiteParticleCoreToFock a u) (finiteParticleCoreToFock a (coreAxisBoostGenerator a v)) := by
  calc
    _ = inner ℂ (axisBoostGeneratorScale a •
        finiteParticleCoreToFock a (coreAxisBoostDifferential a u)) (finiteParticleCoreToFock a v) :=
      congrArg (fun z : FockHilbert a => inner ℂ z (finiteParticleCoreToFock a v))
        (coreAxisBoostGenerator_inclusion a u)
    _ = inner ℂ (finiteParticleCoreToFock a u) (axisBoostGeneratorScale a •
        finiteParticleCoreToFock a (coreAxisBoostDifferential a v)) :=
      UnitaryCore.scaled_skew_pair_symmetric (axisBoostGeneratorScale a) (star_axisBoostGeneratorScale a)
        _ _ _ _ (coreAxisBoostDifferential_skew a u v)
    _ = _ := congrArg (fun z : FockHilbert a => inner ℂ (finiteParticleCoreToFock a u) z)
      (coreAxisBoostGenerator_inclusion a v).symm

def fockCoreAxisBoostGenerator (a : Parameters) : FockHilbert a →ₗ.[ℂ] FockHilbert a where
  domain := fockCoreDomain a
  toFun := ((finiteParticleCoreToFock a).comp (coreAxisBoostGenerator a)).comp
    (fockCoreDomainEquiv a).symm.toLinearMap

theorem fockCoreAxisBoostGenerator_on_original_core (a : Parameters) (u : FiniteParticleCore) :
    fockCoreAxisBoostGenerator a (includedFockCore a u) =
      finiteParticleCoreToFock a (coreAxisBoostGenerator a u) := by
  change finiteParticleCoreToFock a (coreAxisBoostGenerator a
    ((fockCoreDomainEquiv a).symm (fockCoreDomainEquiv a u))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem fockAxisBoost_core_generator_hasDerivAt (a : Parameters) (u : FiniteParticleCore) (r : ℝ) :
    HasDerivAt (fun s => fockAxisBoostUnitary a s (finiteParticleCoreToFock a u))
      ((axisBoostGeneratorScale a)⁻¹ • fockAxisBoostUnitary a r
        (finiteParticleCoreToFock a (coreAxisBoostGenerator a u))) r := by
  have he : fockAxisBoostUnitary a r (finiteParticleCoreToFock a (coreAxisBoostGenerator a u)) =
      axisBoostGeneratorScale a • fockAxisBoostUnitary a r
        (finiteParticleCoreToFock a (coreAxisBoostDifferential a u)) :=
    (congrArg (fun z : FockHilbert a => fockAxisBoostUnitary a r z)
      (coreAxisBoostGenerator_inclusion a u)).trans
      ((fockAxisBoostUnitary a r).map_smul (axisBoostGeneratorScale a) _)
  have ht : (axisBoostGeneratorScale a)⁻¹ • fockAxisBoostUnitary a r
      (finiteParticleCoreToFock a (coreAxisBoostGenerator a u)) =
      fockAxisBoostUnitary a r (finiteParticleCoreToFock a (coreAxisBoostDifferential a u)) := by
    calc
      _ = (axisBoostGeneratorScale a)⁻¹ • (axisBoostGeneratorScale a •
          fockAxisBoostUnitary a r (finiteParticleCoreToFock a (coreAxisBoostDifferential a u))) :=
        congrArg (fun z : FockHilbert a => (axisBoostGeneratorScale a)⁻¹ • z) he
      _ = _ := inv_smul_smul₀ (axisBoostGeneratorScale_ne_zero a) _
  exact ht.symm ▸ fockAxisBoost_original_core_hasDerivAt a u r

end AASCKleinGordon
