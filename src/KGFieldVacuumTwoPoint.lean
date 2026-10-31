import KGSpacetimeFieldEquation
import KGSpacetimeFieldNonvacuity

noncomputable section
set_option maxHeartbeats 2400000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

theorem creation_vacuum_inner (a : Parameters) (f g : 𝓢(Momentum,ℂ)) :
    inner ℂ (finiteParticleCoreToFock a (creationCore f vacuumCore))
      (finiteParticleCoreToFock a (creationCore g vacuumCore)) =
        inner ℂ (oneParticleSchwartzToHilbert a f) (oneParticleSchwartzToHilbert a g) := by
  rw [creation_annihilation_original_core_inner a f vacuumCore (creationCore g vacuumCore)]
  have hc := congrArg (fun L : FiniteParticleCore →ₗ[ℂ] FiniteParticleCore => L vacuumCore)
    (mixed_CCR_core a f g)
  change annihilationCore a f (creationCore g vacuumCore) =
    inner ℂ (oneParticleSchwartzToHilbert a f) (oneParticleSchwartzToHilbert a g) • vacuumCore +
      creationCore g (annihilationCore a f vacuumCore) at hc
  rw [annihilationCore_vacuum_zero, map_zero, add_zero] at hc
  rw [hc, map_smul, inner_smul_right]
  have hΩ : inner ℂ (finiteParticleCoreToFock a vacuumCore)
      (finiteParticleCoreToFock a vacuumCore) = 1 := by
    change inner ℂ (fockVacuum a) (fockVacuum a) = 1
    simp only [inner_self_eq_norm_sq_to_K, fockVacuum_norm]
    norm_num
  rw [hΩ, mul_one]

theorem spacetimeFieldCore_on_vacuum (a : Parameters) (s : ℝ) (h : 𝓢(Spacetime,ℂ)) :
    spacetimeFieldCore a s h vacuumCore =
      (s : ℂ) • creationCore (spacetimeSmearingCLM a h) vacuumCore := by
  simp only [spacetimeFieldCore, LinearMap.smul_apply, LinearMap.add_apply,
    annihilationCore_vacuum_zero, add_zero]

/-- An absolutely convergent pairing of Schwartz restrictions. This is not
an asserted pointwise value of an unsmeared mass-shell oscillatory integral. -/
def massShellTwoPointPairing (a : Parameters) (h k : 𝓢(Spacetime,ℂ)) : ℂ :=
  ∫ p, star (spacetimeSmearingCLM a (conjugateSchwartzCLM h) p) *
    spacetimeSmearingCLM a k p ∂wignerMeasure a

theorem massShellTwoPointPairing_integrable (a : Parameters) (h k : 𝓢(Spacetime,ℂ)) :
    Integrable (fun p => star (spacetimeSmearingCLM a (conjugateSchwartzCLM h) p) *
      spacetimeSmearingCLM a k p) (wignerMeasure a) :=
  schwartz_pair_integrable _ _ _

theorem massShellTwoPointPairing_eq_inner (a : Parameters) (h k : 𝓢(Spacetime,ℂ)) :
    massShellTwoPointPairing a h k =
      inner ℂ (oneParticleSchwartzToHilbert a (spacetimeSmearingCLM a (conjugateSchwartzCLM h)))
        (oneParticleSchwartzToHilbert a (spacetimeSmearingCLM a k)) :=
  test_pair_integral_eq_inner _ _ _

theorem spacetimeField_vacuum_two_point (a : Parameters) (s : ℝ) (h k : 𝓢(Spacetime,ℂ)) :
    inner ℂ (finiteParticleCoreToFock a vacuumCore)
      (finiteParticleCoreToFock a (spacetimeFieldCore a s h (spacetimeFieldCore a s k vacuumCore))) =
        (s : ℂ)^2 * massShellTwoPointPairing a h k := by
  have hadj := spacetimeFieldCore_adjoint_test a s (conjugateSchwartzCLM h)
    vacuumCore (spacetimeFieldCore a s k vacuumCore)
  rw [conjugateSchwartz_involutive] at hadj
  rw [← hadj, spacetimeFieldCore_on_vacuum, spacetimeFieldCore_on_vacuum,
    map_smul, map_smul, inner_smul_left, inner_smul_right,
    creation_vacuum_inner, massShellTwoPointPairing_eq_inner]
  simp only [Complex.conj_ofReal]
  ring

theorem fieldCommutatorCoefficient_eq_shell_pairing (a : Parameters) (s : ℝ)
    (h k : 𝓢(Spacetime,ℂ)) :
    fieldCommutatorCoefficient a s h k =
      (s : ℂ)^2 * (massShellTwoPointPairing a h k - massShellTwoPointPairing a k h) := by
  simp only [fieldCommutatorCoefficient, massShellTwoPointPairing_eq_inner]

theorem massShellTwoPointPairing_kleinGordon_left (a : Parameters) (h k : 𝓢(Spacetime,ℂ)) :
    massShellTwoPointPairing a (kleinGordonSchwartzCLM a h) k = 0 := by
  rw [massShellTwoPointPairing_eq_inner, spacetimeSmearing_conjugate_kleinGordon_zero,
    map_zero, inner_zero_left]

theorem massShellTwoPointPairing_kleinGordon_right (a : Parameters) (h k : 𝓢(Spacetime,ℂ)) :
    massShellTwoPointPairing a h (kleinGordonSchwartzCLM a k) = 0 := by
  rw [massShellTwoPointPairing_eq_inner, spacetimeSmearing_kleinGordon_zero,
    map_zero, inner_zero_right]

theorem exists_real_original_fock_field_vacuum_excitation (a : Parameters) (s : ℝ) (hs : s ≠ 0) :
    ∃ h : 𝓢(Spacetime,ℂ), conjugateSchwartzCLM h = h ∧
      fockSpacetimeField a s h (includedFockCore a vacuumCore) ≠ 0 := by
  obtain ⟨h, hr, hn⟩ := exists_real_field_vacuum_excitation a s hs
  refine ⟨h, hr, ?_⟩
  rw [fockSpacetimeField_on_original_core]
  intro hz
  exact hn (finiteParticleCoreToFock_injective a (hz.trans (map_zero _).symm))

end AASCKleinGordon
