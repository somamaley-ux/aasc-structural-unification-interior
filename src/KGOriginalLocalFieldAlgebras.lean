import KGOriginalShellCausalSupport
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

noncomputable section
set_option maxHeartbeats 1200000
open scoped SchwartzMap
namespace AASCKleinGordon

/-- Actual original-core smeared fields supported in a region. -/
def originalLocalFieldGenerators (a : Parameters) (s : ℝ) (O : Set Spacetime) :
    Set (Module.End ℂ FiniteParticleCore) :=
  {A | ∃ h : 𝓢(Spacetime,ℂ), HasCompactSupport (h : Spacetime → ℂ) ∧
    tsupport (h : Spacetime → ℂ) ⊆ O ∧ A=spacetimeFieldCore a s h}

/-- Represented finite local field polynomials on the existing invariant core.
No completion or coincident-point Wick product is introduced here. -/
def originalLocalFieldAlgebra (a : Parameters) (s : ℝ) (O : Set Spacetime) :
    Subalgebra ℂ (Module.End ℂ FiniteParticleCore) :=
  Algebra.adjoin ℂ (originalLocalFieldGenerators a s O)

theorem originalField_mem_localFieldAlgebra (a : Parameters) (s : ℝ) (O : Set Spacetime)
    (h : 𝓢(Spacetime,ℂ)) (hc : HasCompactSupport (h : Spacetime → ℂ))
    (hs : tsupport (h : Spacetime → ℂ) ⊆ O) :
    spacetimeFieldCore a s h ∈ originalLocalFieldAlgebra a s O :=
  Algebra.subset_adjoin ⟨h,hc,hs,rfl⟩

theorem originalLocalFieldGenerators_commute_of_spacelike
    (a : Parameters) (s : ℝ) (O U : Set Spacetime)
    (hs : ∀ x ∈ O, ∀ y ∈ U, 0 < spacetimeMinkowskiSquare (y-x))
    (A B : Module.End ℂ FiniteParticleCore)
    (hA : A ∈ originalLocalFieldGenerators a s O)
    (hB : B ∈ originalLocalFieldGenerators a s U) : Commute A B := by
  obtain ⟨h,hh,hO,rfl⟩ := hA
  obtain ⟨k,hk,kU,rfl⟩ := hB
  change (spacetimeFieldCore a s h).comp (spacetimeFieldCore a s k)=
    (spacetimeFieldCore a s k).comp (spacetimeFieldCore a s h)
  apply spacetimeFieldCore_locality a s h k hh hk
  intro x hx y hy
  exact hs x (hO hx) y (kU hy)

/-- Every two finite local field polynomials in spacelike separated regions
commute on the original core. This is cross-region commutation, not internal
commutativity of an individual region's algebra or bounded irreducibility. -/
theorem originalLocalFieldAlgebras_commute_of_spacelike
    (a : Parameters) (s : ℝ) (O U : Set Spacetime)
    (hs : ∀ x ∈ O, ∀ y ∈ U, 0 < spacetimeMinkowskiSquare (y-x))
    (A B : Module.End ℂ FiniteParticleCore)
    (hA : A ∈ originalLocalFieldAlgebra a s O)
    (hB : B ∈ originalLocalFieldAlgebra a s U) : Commute A B := by
  apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute hB
  intro B hB
  apply Commute.symm
  apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute hA
  intro A hA
  exact (originalLocalFieldGenerators_commute_of_spacelike a s O U hs A B hA hB).symm

theorem shellSineNormalization_ne_zero (a : Parameters) : shellSineNormalization a ≠ 0 := by
  have hm : a.mass*a.speed/a.hbar ≠ 0 :=
    div_ne_zero (mul_ne_zero a.mass_pos.ne' a.speed_pos.ne') a.hbar_pos.ne'
  have hL : 2*Real.pi*a.hbar ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) a.hbar_pos.ne'
  unfold shellSineNormalization
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr hm))
    (Complex.ofReal_ne_zero.mpr (pow_ne_zero 3 hL))

/-- The causal-support result concerns the earlier nonzero shell functional. -/
theorem original_causal_shell_is_nonzero (a : Parameters) : massShellCommutatorCLM a ≠ 0 :=
  massShellCommutator_nonzero a

end AASCKleinGordon
