import KGMassShell
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Algebra.DirectSum.Module

/-! The actual algebraic bosonic finite-particle Schwartz domain from current
Module B section24.1. Each n-particle component is a symmetric Schwartz
function on continuous momentum configurations. This file constructs that
domain and occupied sectors; its Hilbert completion and field operations
are separate remaining constructions. -/
noncomputable section
open scoped SchwartzMap ContDiff DirectSum
namespace AASCKleinGordon

abbrev ParticleConfiguration (n : ℕ) := Fin n → Momentum

def bosonicSchwartz (n : ℕ) : Submodule ℂ 𝓢(ParticleConfiguration n,ℂ) where
  carrier := {f | ∀ σ : Equiv.Perm (Fin n), ∀ x, f (fun i => x (σ i))=f x}
  zero_mem' := by intro σ x; rfl
  add_mem' := by
    intro f g hf hg σ x
    change f (fun i => x (σ i))+g (fun i => x (σ i))=f x+g x
    rw [hf,hg]
  smul_mem' := by
    intro c f hf σ x
    change c*f (fun i => x (σ i))=c*f x
    rw [hf]

abbrev FiniteParticleCore := ⨁ n : ℕ, bosonicSchwartz n

def vacuumSchwartz : 𝓢(ParticleConfiguration 0,ℂ) :=
  (HasCompactSupport.of_compactSpace (fun _ : ParticleConfiguration 0 => (1 : ℂ))).toSchwartzMap
    contDiff_const

def vacuumSector : bosonicSchwartz 0 := ⟨vacuumSchwartz,by intro σ x; rfl⟩

def vacuumCore : FiniteParticleCore :=
  DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) 0 vacuumSector

theorem vacuumCore_nonzero : vacuumCore≠0 := by
  intro h
  have he := congrArg (fun v : FiniteParticleCore => ((v 0).val) 0) h
  simp [vacuumCore,DirectSum.lof_apply,vacuumSector,vacuumSchwartz] at he

theorem exists_nonzero_one_particle_schwartz :
    ∃ f : 𝓢(ParticleConfiguration 1,ℂ), f 0=1 := by
  obtain ⟨f,_,hc,hs,_,h0⟩ := exists_contDiff_tsupport_subset
    (E:=ParticleConfiguration 1) (x:=0) (n:=⊤) (s:=Set.univ) (by simp)
  have hcc : HasCompactSupport (fun x => (f x : ℂ)) :=
    hc.comp_left (g:=Complex.ofReal) (by simp)
  have hsc : ContDiff ℝ ∞ (fun x => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hs
  exact ⟨hcc.toSchwartzMap hsc,by simpa using congrArg Complex.ofReal h0⟩

def oneParticleSchwartz : 𝓢(ParticleConfiguration 1,ℂ) :=
  Classical.choose exists_nonzero_one_particle_schwartz

theorem oneParticleSchwartz_at_zero : oneParticleSchwartz 0=1 :=
  Classical.choose_spec exists_nonzero_one_particle_schwartz

def oneParticleSector : bosonicSchwartz 1 := ⟨oneParticleSchwartz,by
  intro σ x
  have hx : (fun i => x (σ i))=x :=
    funext (fun i => congrArg x (Subsingleton.elim (σ i) i))
  rw [hx]⟩

def oneParticleCore : FiniteParticleCore :=
  DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) 1 oneParticleSector

theorem oneParticleCore_nonzero : oneParticleCore≠0 := by
  intro h
  have he := congrArg (fun v : FiniteParticleCore => ((v 1).val) 0) h
  simp [oneParticleCore,DirectSum.lof_apply,oneParticleSector,oneParticleSchwartz_at_zero] at he

theorem vacuum_and_particle_distinct : vacuumCore≠oneParticleCore := by
  intro h
  have he := congrArg (fun v : FiniteParticleCore => ((v 0).val) 0) h
  simp [vacuumCore,oneParticleCore,DirectSum.lof_eq_of,DirectSum.of_apply,
    vacuumSector,vacuumSchwartz] at he

end AASCKleinGordon
