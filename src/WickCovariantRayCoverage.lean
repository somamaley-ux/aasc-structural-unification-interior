import WickOperationalKernelUniqueness
import WickCalibratedSourceRole

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped SchwartzMap
namespace AASCKleinGordon

/-- An ORIGINAL sector condition, independent of the covariant map's image. -/
def WickOriginalOneSector (u : FiniteParticleCore) : Prop :=
  ∀ n : ℕ, n ≠ 1 → u n = 0

theorem wick_one_core_component_one (v : bosonicSchwartz 1) :
    wickOneCoreCLM v 1 = v := by
  change DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) 1 v 1 = v
  simp only [DirectSum.lof_eq_of, DirectSum.of_eq_same]

theorem wick_one_core_component_other (v : bosonicSchwartz 1) (n : ℕ) (hn : n ≠ 1) :
    wickOneCoreCLM v n = 0 := by
  change DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) 1 v n = 0
  simp only [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hn]

theorem wick_one_sector_reconstruct (u : FiniteParticleCore) (hu : WickOriginalOneSector u) :
    wickOneCoreCLM (u 1) = u := by
  apply DirectSum.ext
  intro n
  by_cases hn : n = 1
  · subst n
    exact wick_one_core_component_one _
  · rw [wick_one_core_component_other _ n hn, hu n hn]

theorem wick_covariant_core_has_original_one_sector (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    WickOriginalOneSector (wickCovariantOriginalCore a f) := by
  intro n hn
  exact wick_one_core_component_other (wickCovariantOriginalSector a f) n hn

def wickCovariantSectorCoordinates (a : Parameters) (v : bosonicSchwartz 1) : 𝓢(Momentum,ℂ) :=
  wickCovariantSchwartz a (sectorOneToSchwartz v)

theorem wick_covariant_sector_coordinates_left (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    wickCovariantSectorCoordinates a (wickCovariantOriginalSector a f) = f :=
  wick_covariant_original_sector_wavefunction a f

theorem wick_covariant_sector_coordinates_right (a : Parameters) (v : bosonicSchwartz 1) :
    wickCovariantOriginalSector a (wickCovariantSectorCoordinates a v) = v := by
  obtain ⟨f,rfl⟩ := wick_covariant_original_sector_surjective a v
  rw [wick_covariant_sector_coordinates_left]

theorem wick_covariant_original_core_injective (a : Parameters) :
    Function.Injective (wickCovariantOriginalCore a) := by
  intro f g h
  have hs := congrArg (fun u : FiniteParticleCore => u 1) h
  change wickOneCoreCLM (wickCovariantOriginalSector a f) 1 =
    wickOneCoreCLM (wickCovariantOriginalSector a g) 1 at hs
  rw [wick_one_core_component_one, wick_one_core_component_one] at hs
  exact (wick_covariant_sector_coordinates_left a f).symm.trans
    ((congrArg (wickCovariantSectorCoordinates a) hs).trans
      (wick_covariant_sector_coordinates_left a g))

theorem wick_covariant_core_coverage_iff (a : Parameters) (u : FiniteParticleCore) :
    (∃ f : 𝓢(Momentum,ℂ), wickCovariantOriginalCore a f = u) ↔ WickOriginalOneSector u := by
  constructor
  · rintro ⟨f,rfl⟩
    exact wick_covariant_core_has_original_one_sector a f
  · intro hu
    refine ⟨wickCovariantSectorCoordinates a (u 1), ?_⟩
    change wickOneCoreCLM (wickCovariantOriginalSector a (wickCovariantSectorCoordinates a (u 1))) = u
    rw [wick_covariant_sector_coordinates_right]
    exact wick_one_sector_reconstruct u hu

theorem wick_original_one_sector_smul (c : ℂ) (u : FiniteParticleCore)
    (hu : WickOriginalOneSector u) : WickOriginalOneSector (c • u) := by
  intro n hn
  change c • u n = 0
  rw [hu n hn, smul_zero]

theorem wick_original_one_sector_smul_iff (c : ℂ) (hc : c ≠ 0) (u : FiniteParticleCore) :
    WickOriginalOneSector (c • u) ↔ WickOriginalOneSector u := by
  constructor
  · intro h
    have hi := wick_original_one_sector_smul c⁻¹ (c • u) h
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hi
  · exact wick_original_one_sector_smul c u

abbrev WickCovariantNonzeroTest := {f : 𝓢(Momentum,ℂ) // f ≠ 0}

def wickCovariantRaySetoid : Setoid WickCovariantNonzeroTest where
  r u v := ∃ z : ℂ, z ≠ 0 ∧ v.val = z • u.val
  iseqv := by
    refine ⟨?_,?_,?_⟩
    · intro u
      exact ⟨1,one_ne_zero,by simp⟩
    · rintro u v ⟨z,hz,hv⟩
      exact ⟨z⁻¹,inv_ne_zero hz,by rw [hv,smul_smul,inv_mul_cancel₀ hz,one_smul]⟩
    · rintro u v w ⟨z,hz,hv⟩ ⟨r,hr,hw⟩
      exact ⟨r*z,mul_ne_zero hr hz,by rw [hw,hv,smul_smul]⟩

def wickCovariantNonzeroCore (a : Parameters) (f : WickCovariantNonzeroTest) : WickNonzeroCore :=
  ⟨wickCovariantOriginalCore a f.val, wick_covariant_original_core_nonzero a f.val f.property⟩

theorem wick_covariant_core_ray_iff (a : Parameters) (u v : WickCovariantNonzeroTest) :
    wickCoreRaySetoid.r (wickCovariantNonzeroCore a u) (wickCovariantNonzeroCore a v) ↔
      wickCovariantRaySetoid.r u v := by
  constructor
  · rintro ⟨z,hz,h⟩
    refine ⟨z,hz,wick_covariant_original_core_injective a ?_⟩
    exact h.trans ((wickCovariantOriginalCore a).map_smul z u.val).symm
  · rintro ⟨z,hz,h⟩
    exact ⟨z,hz,(congrArg (wickCovariantOriginalCore a) h).trans
      ((wickCovariantOriginalCore a).map_smul z u.val)⟩

def wickCovariantOriginalRay (a : Parameters) :
    Quotient wickCovariantRaySetoid → Quotient wickCoreRaySetoid :=
  Quotient.map (wickCovariantNonzeroCore a) (fun u v h => (wick_covariant_core_ray_iff a u v).mpr h)

theorem wick_covariant_original_ray_injective (a : Parameters) :
    Function.Injective (wickCovariantOriginalRay a) := by
  intro r t h
  induction r using Quotient.inductionOn with | _ u =>
    induction t using Quotient.inductionOn with | _ v =>
      exact Quotient.sound ((wick_covariant_core_ray_iff a u v).mp (Quotient.exact h))

theorem wick_covariant_nonzero_core_coverage (a : Parameters) (u : WickNonzeroCore) :
    (∃ f : WickCovariantNonzeroTest, wickCovariantNonzeroCore a f = u) ↔
      WickOriginalOneSector u.val := by
  constructor
  · rintro ⟨f,h⟩
    rw [← h]
    exact wick_covariant_core_has_original_one_sector a f.val
  · intro hu
    obtain ⟨f,hf⟩ := (wick_covariant_core_coverage_iff a u.val).mpr hu
    have hn : f ≠ 0 := by
      intro hz
      apply u.property
      rw [← hf,hz,map_zero]
    exact ⟨⟨f,hn⟩,Subtype.ext hf⟩

def WickOriginalOneRay (r : Quotient wickCoreRaySetoid) : Prop :=
  ∃ u : WickNonzeroCore, Quotient.mk wickCoreRaySetoid u = r ∧ WickOriginalOneSector u.val

theorem wick_covariant_original_ray_coverage (a : Parameters) (q : Quotient wickCoreRaySetoid) :
    (∃ r, wickCovariantOriginalRay a r = q) ↔ WickOriginalOneRay q := by
  constructor
  · rintro ⟨r,rfl⟩
    refine ⟨wickCovariantNonzeroCore a r.out, ?_, wick_covariant_core_has_original_one_sector a r.out.val⟩
    exact congrArg (wickCovariantOriginalRay a) (Quotient.out_eq r)
  · rintro ⟨u,hu,hs⟩
    obtain ⟨f,hf⟩ := (wick_covariant_nonzero_core_coverage a u).mpr hs
    exact ⟨Quotient.mk wickCovariantRaySetoid f,
      (congrArg (Quotient.mk wickCoreRaySetoid) hf).trans hu⟩

theorem wick_vacuum_not_original_one_sector : ¬ WickOriginalOneSector vacuumCore := by
  intro h
  have he := congrArg (fun v : bosonicSchwartz 0 => v.val 0) (h 0 (by decide))
  simp [vacuumCore,DirectSum.lof_eq_of,vacuumSector,vacuumSchwartz] at he

end AASCKleinGordon
