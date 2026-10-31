import KGParticleMeasureControl
import Mathlib.Algebra.DirectSum.Module

noncomputable section
open MeasureTheory Filter
open scoped SchwartzMap DirectSum
namespace AASCKleinGordon

theorem particlePermutation_apply (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : ParticleConfiguration n) (i : Fin n) : particlePermutation n σ x i=x (σ.symm i) := by
  simpa [particlePermutation] using
    MeasurableEquiv.piCongrLeft_apply_apply (β:=fun _ : Fin n => Momentum) σ x (σ.symm i)

theorem bosonic_schwartz_fixed_by_particlePermutation (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (f : bosonicSchwartz n) (x : ParticleConfiguration n) :
    f.val (particlePermutation n σ x)=f.val x := by
  have he : particlePermutation n σ x=(fun i => x (σ.symm i)) :=
    funext (particlePermutation_apply n σ x)
  rw [he]
  exact f.property σ.symm x

theorem bosonic_core_image_fixed (a : Parameters) (n : ℕ) (f : bosonicSchwartz n)
    (σ : Equiv.Perm (Fin n)) :
    permutationUnitary a n σ (particleSchwartzToHilbert a n f.val)=
      particleSchwartzToHilbert a n f.val := by
  change Lp.compMeasurePreserving (particlePermutation n σ)
    (particlePermutation_preserves_measure a n σ) (particleSchwartzToHilbert a n f.val)=_
  apply Lp.ext
  have h₁ := Lp.coeFn_compMeasurePreserving (particleSchwartzToHilbert a n f.val)
    (particlePermutation_preserves_measure a n σ)
  have h₂ := (particlePermutation_preserves_measure a n σ).quasiMeasurePreserving.ae
    (f.val.coeFn_toLp 2 (particleMeasure a n))
  have h₃ := f.val.coeFn_toLp 2 (particleMeasure a n)
  filter_upwards [h₁,h₂,h₃] with x hx hy hz
  exact hx.trans (hy.trans ((bosonic_schwartz_fixed_by_particlePermutation n σ f x).trans hz.symm))

def bosonicCoreToSector (a : Parameters) (n : ℕ) : bosonicSchwartz n →L[ℂ] bosonicHilbertSector a n :=
  ((particleSchwartzToHilbert a n).comp (bosonicSchwartz n).subtypeL).codRestrict
    (bosonicHilbertSector a n) (fun f => (bosonicHilbertSector_mem a n _).2 (bosonic_core_image_fixed a n f))

theorem bosonicCoreToSector_injective (a : Parameters) (n : ℕ) :
    Function.Injective (bosonicCoreToSector a n) := by
  intro f g h
  apply Subtype.ext
  apply particleSchwartzToHilbert_injective a n
  exact congrArg Subtype.val h

def finiteParticleCoreToFock (a : Parameters) : FiniteParticleCore →ₗ[ℂ] FockHilbert a :=
  DirectSum.toModule ℂ ℕ (FockHilbert a) (fun n =>
    (lp.singleContinuousLinearMap ℂ (fun k : ℕ => bosonicHilbertSector a k) 2 n).toLinearMap.comp
      (bosonicCoreToSector a n).toLinearMap)

theorem finiteParticleCoreToFock_on_sector (a : Parameters) (n : ℕ) (f : bosonicSchwartz n) :
    finiteParticleCoreToFock a (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n f)=
      lp.single 2 n (bosonicCoreToSector a n f) := by
  exact DirectSum.toModule_lof _ _ _

end AASCKleinGordon
