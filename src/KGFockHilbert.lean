import KGOneParticleHilbert
import LpMeasureEquivalence
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! The actual weighted n-particle Hilbert spaces, permutation unitaries,
closed symmetric sectors and full countable Hilbert Fock sum. No density or
field/EMT certificate is an input. Connection of the algebraic Schwartz
core and the field operators is proved separately. -/
noncomputable section
open MeasureTheory
namespace AASCKleinGordon

def particleMeasure (a : Parameters) (n : ℕ) : Measure (ParticleConfiguration n) :=
  Measure.pi (fun _ : Fin n => wignerMeasure a)

abbrev ParticleHilbert (a : Parameters) (n : ℕ) := Lp ℂ 2 (particleMeasure a n)

def particlePermutation (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ParticleConfiguration n ≃ᵐ ParticleConfiguration n :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin n => Momentum) σ

theorem particlePermutation_preserves_measure (a : Parameters) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (particlePermutation n σ) (particleMeasure a n) (particleMeasure a n) := by
  exact measurePreserving_piCongrLeft (fun _ : Fin n => wignerMeasure a) σ

theorem particlePermutation_inverse_preserves_measure (a : Parameters) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (particlePermutation n σ).symm (particleMeasure a n) (particleMeasure a n) := by
  exact MeasurePreserving.symm (particlePermutation n σ) (particlePermutation_preserves_measure a n σ)

def permutationUnitary (a : Parameters) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ParticleHilbert a n ≃ₗᵢ[ℂ] ParticleHilbert a n :=
  lpMeasureEquivalence (particlePermutation n σ) (particlePermutation_preserves_measure a n σ)
    (particlePermutation_inverse_preserves_measure a n σ)

def bosonicHilbertSector (a : Parameters) (n : ℕ) : Submodule ℂ (ParticleHilbert a n) :=
  ⨅ σ : Equiv.Perm (Fin n),
    ((permutationUnitary a n σ).toLinearIsometry.toContinuousLinearMap-
      ContinuousLinearMap.id ℂ (ParticleHilbert a n)).ker

theorem bosonicHilbertSector_closed (a : Parameters) (n : ℕ) :
    IsClosed (bosonicHilbertSector a n : Set (ParticleHilbert a n)) := by
  unfold bosonicHilbertSector
  simp only [Submodule.coe_iInf]
  exact isClosed_iInter (fun σ => ContinuousLinearMap.isClosed_ker _)

theorem bosonicHilbertSector_mem (a : Parameters) (n : ℕ) (f : ParticleHilbert a n) :
    f ∈ bosonicHilbertSector a n ↔ ∀ σ,permutationUnitary a n σ f=f := by
  simp [bosonicHilbertSector,Submodule.mem_iInf,sub_eq_zero]

instance bosonicHilbertSector_complete (a : Parameters) (n : ℕ) :
    CompleteSpace (bosonicHilbertSector a n) := (bosonicHilbertSector_closed a n).completeSpace_coe

abbrev FockHilbert (a : Parameters) := lp (fun n : ℕ => bosonicHilbertSector a n) 2

end AASCKleinGordon
