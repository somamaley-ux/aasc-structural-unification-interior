import KGFieldVacuumTwoPoint

noncomputable section
set_option maxHeartbeats 2400000
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

theorem massShellTwoPointPairing_add_left (a : Parameters) (h k l : 𝓢(Spacetime,ℂ)) :
    massShellTwoPointPairing a (h+k) l =
      massShellTwoPointPairing a h l + massShellTwoPointPairing a k l := by
  simp only [massShellTwoPointPairing_eq_inner, map_add, inner_add_left]

theorem massShellTwoPointPairing_smul_left (a : Parameters) (c : ℂ) (h k : 𝓢(Spacetime,ℂ)) :
    massShellTwoPointPairing a (c • h) k = c * massShellTwoPointPairing a h k := by
  simp only [massShellTwoPointPairing_eq_inner, conjugateSchwartz_smul, map_smul,
    inner_smul_left, starRingEnd_apply, star_star]

theorem massShellTwoPointPairing_add_right (a : Parameters) (h k l : 𝓢(Spacetime,ℂ)) :
    massShellTwoPointPairing a h (k+l) =
      massShellTwoPointPairing a h k + massShellTwoPointPairing a h l := by
  simp only [massShellTwoPointPairing_eq_inner, map_add, inner_add_right]

theorem massShellTwoPointPairing_smul_right (a : Parameters) (c : ℂ) (h k : 𝓢(Spacetime,ℂ)) :
    massShellTwoPointPairing a h (c • k) = c * massShellTwoPointPairing a h k := by
  simp only [massShellTwoPointPairing_eq_inner, map_smul, inner_smul_right]

theorem massShellTwoPointPairing_joint_continuous (a : Parameters) :
    Continuous (fun hk : 𝓢(Spacetime,ℂ) × 𝓢(Spacetime,ℂ) =>
      massShellTwoPointPairing a hk.1 hk.2) := by
  simp_rw [massShellTwoPointPairing_eq_inner]
  exact ((oneParticleSchwartzToHilbert a).continuous.comp
      ((spacetimeSmearingCLM a).continuous.comp
        (conjugateSchwartzCLM.continuous.comp continuous_fst))).inner
    ((oneParticleSchwartzToHilbert a).continuous.comp
      ((spacetimeSmearingCLM a).continuous.comp continuous_snd))

/-- Vacuum normal ordering of a pair of actual smeared fields on the same core.
This does not yet perform a local coincident-point EMT construction. -/
def normalOrderedFieldPairCore (a : Parameters) (s : ℝ) (h k : 𝓢(Spacetime,ℂ)) :
    FiniteParticleCore →ₗ[ℂ] FiniteParticleCore :=
  (spacetimeFieldCore a s h).comp (spacetimeFieldCore a s k) -
    ((s : ℂ)^2 * massShellTwoPointPairing a h k) • LinearMap.id

theorem normalOrderedFieldPairCore_symmetric (a : Parameters) (s : ℝ)
    (h k : 𝓢(Spacetime,ℂ)) :
    normalOrderedFieldPairCore a s h k = normalOrderedFieldPairCore a s k h := by
  rw [normalOrderedFieldPairCore, spacetimeFieldCore_CCR,
    fieldCommutatorCoefficient_eq_shell_pairing, normalOrderedFieldPairCore]
  module

theorem normalOrderedFieldPairCore_state_continuous (a : Parameters) (s : ℝ)
    (h k : 𝓢(Spacetime,ℂ)) : Continuous (normalOrderedFieldPairCore a s h k) := by
  exact ((spacetimeFieldCore_state_continuous a s h).comp
    (spacetimeFieldCore_state_continuous a s k)).sub
      (continuous_id.const_smul ((s : ℂ)^2 * massShellTwoPointPairing a h k))

theorem normalOrderedFieldPairCore_vacuum_mean_zero (a : Parameters) (s : ℝ)
    (h k : 𝓢(Spacetime,ℂ)) :
    inner ℂ (finiteParticleCoreToFock a vacuumCore)
      (finiteParticleCoreToFock a (normalOrderedFieldPairCore a s h k vacuumCore)) = 0 := by
  simp only [normalOrderedFieldPairCore, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.id_coe, id_eq, map_sub, map_smul,
    inner_sub_right, inner_smul_right]
  rw [spacetimeField_vacuum_two_point a s h k]
  have hΩ : inner ℂ (finiteParticleCoreToFock a vacuumCore)
      (finiteParticleCoreToFock a vacuumCore) = 1 := by
    change inner ℂ (fockVacuum a) (fockVacuum a) = 1
    simp only [inner_self_eq_norm_sq_to_K, fockVacuum_norm]
    norm_num
  rw [hΩ, mul_one, sub_self]

theorem normalOrderedFieldPairCore_kleinGordon_left (a : Parameters) (s : ℝ)
    (h k : 𝓢(Spacetime,ℂ)) :
    normalOrderedFieldPairCore a s (kleinGordonSchwartzCLM a h) k = 0 := by
  rw [normalOrderedFieldPairCore, spacetimeFieldCore_kleinGordon,
    massShellTwoPointPairing_kleinGordon_left]
  simp only [LinearMap.zero_comp, mul_zero, zero_smul]
  exact sub_self (0 : FiniteParticleCore →ₗ[ℂ] FiniteParticleCore)

theorem normalOrderedFieldPairCore_kleinGordon_right (a : Parameters) (s : ℝ)
    (h k : 𝓢(Spacetime,ℂ)) :
    normalOrderedFieldPairCore a s h (kleinGordonSchwartzCLM a k) = 0 := by
  rw [normalOrderedFieldPairCore, spacetimeFieldCore_kleinGordon,
    massShellTwoPointPairing_kleinGordon_right]
  simp only [LinearMap.comp_zero, mul_zero, zero_smul]
  exact sub_self (0 : FiniteParticleCore →ₗ[ℂ] FiniteParticleCore)

end AASCKleinGordon
