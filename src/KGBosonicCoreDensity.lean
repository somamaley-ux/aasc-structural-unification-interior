import KGSchwartzSymmetrization

noncomputable section
open MeasureTheory Set
open scoped SchwartzMap
namespace AASCKleinGordon

theorem hilbertSymmetrizer_range_bosonic (a : Parameters) (n : ℕ) (f : ParticleHilbert a n) :
    hilbertSymmetrizer a n f ∈ bosonicHilbertSector a n := by
  have hc : IsClosed {f | hilbertSymmetrizer a n f ∈ bosonicHilbertSector a n} :=
    (bosonicHilbertSector_closed a n).preimage (hilbertSymmetrizer a n).continuous
  have hs : Set.range (particleSchwartzToHilbert a n) ⊆
      {f | hilbertSymmetrizer a n f ∈ bosonicHilbertSector a n} := by
    rintro z ⟨g,rfl⟩
    change hilbertSymmetrizer a n (particleSchwartzToHilbert a n g) ∈ bosonicHilbertSector a n
    rw [← symmetrizer_intertwines]
    exact (bosonicCoreToSector a n ⟨schwartzSymmetrizer n g,schwartzSymmetrizer_bosonic n g⟩).property
  exact closure_minimal hs hc ((particleSchwartzToHilbert_dense a n) f)

theorem hilbertSymmetrizer_fixed (a : Parameters) (n : ℕ) (f : bosonicHilbertSector a n) :
    hilbertSymmetrizer a n f.val=f.val := by
  have hfix : ∀ σ : Equiv.Perm (Fin n),permutationUnitary a n σ.symm f.val=f.val :=
    fun σ => (bosonicHilbertSector_mem a n _).1 f.property σ.symm
  have hN : (Fintype.card (Equiv.Perm (Fin n)) : ℂ)≠0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [hilbertSymmetrizer,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply]
  change permutationAverageCoefficient n • (∑ σ : Equiv.Perm (Fin n),permutationUnitary a n σ.symm f.val)=f.val
  simp only [hfix,Finset.sum_const,Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  simp [permutationAverageCoefficient,smul_smul,hN]

def hilbertBosonicProjection (a : Parameters) (n : ℕ) :
    ParticleHilbert a n →L[ℂ] bosonicHilbertSector a n :=
  (hilbertSymmetrizer a n).codRestrict (bosonicHilbertSector a n) (hilbertSymmetrizer_range_bosonic a n)

theorem hilbertBosonicProjection_surjective (a : Parameters) (n : ℕ) :
    Function.Surjective (hilbertBosonicProjection a n) := by
  intro f
  exact ⟨f.val,Subtype.ext (hilbertSymmetrizer_fixed a n f)⟩

theorem bosonicCoreToSector_dense (a : Parameters) (n : ℕ) : DenseRange (bosonicCoreToSector a n) := by
  have hd := (hilbertBosonicProjection_surjective a n).denseRange.comp
    (particleSchwartzToHilbert_dense a n) (hilbertBosonicProjection a n).continuous
  intro f
  apply closure_mono ?_ (hd f)
  rintro z ⟨g,rfl⟩
  refine ⟨⟨schwartzSymmetrizer n g,schwartzSymmetrizer_bosonic n g⟩,?_⟩
  apply Subtype.ext
  exact symmetrizer_intertwines a n g

end AASCKleinGordon
