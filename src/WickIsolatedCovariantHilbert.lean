import WickOneSectorHilbert

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

def wickOneSectorIsolated (a : Parameters) :
    bosonicHilbertSector a 1 ≃ₗᵢ[ℂ] wickIsolatedOneParticleSpace a where
  toFun f := ⟨lp.single (E := fun n : ℕ => bosonicHilbertSector a n) 2 1 f,by
    apply (wick_isolated_one_particle_space_iff a _).mpr
    intro n hn
    exact lp.single_apply_ne (E := fun n : ℕ => bosonicHilbertSector a n) 2 1 f hn⟩
  invFun f := f.val 1
  left_inv f := lp.single_apply_self (E := fun n : ℕ => bosonicHilbertSector a n) 2 1 f
  right_inv f := by
    apply Subtype.ext
    apply lp.ext
    funext n
    by_cases hn : n=1
    · subst n
      exact lp.single_apply_self (E := fun n : ℕ => bosonicHilbertSector a n) 2 1 (f.val 1)
    · rw [lp.single_apply_ne (E := fun n : ℕ => bosonicHilbertSector a n) 2 1 (f.val 1) hn]
      exact ((wick_isolated_one_particle_space_iff a f.val).mp f.property n hn).symm
  map_add' f g := Subtype.ext (lp.single_add (E := fun n : ℕ => bosonicHilbertSector a n) 2 1 f g)
  map_smul' c f := Subtype.ext (lp.single_smul (E := fun n : ℕ => bosonicHilbertSector a n) 2 1 c f)
  norm_map' f := by
    change ‖lp.single (E := fun n : ℕ => bosonicHilbertSector a n) 2 1 f‖=‖f‖
    exact lp.norm_single (E := fun n : ℕ => bosonicHilbertSector a n) (p := 2) (by norm_num) 1 f

def wickWignerToIsolated (a : Parameters) :
    OneParticleHilbert a ≃ₗᵢ[ℂ] wickIsolatedOneParticleSpace a :=
  (wickOneSectorCoordinates a).trans (wickOneSectorIsolated a)

def wickIsolatedCovariantHilbert (a : Parameters) :
    wickIsolatedOneParticleSpace a ≃ₗᵢ[ℂ] WickCovariantHilbert a :=
  (wickWignerToIsolated a).symm.trans (wickCovariantNormalization a)

theorem wick_isolated_reconstruct (a : Parameters) (f : wickIsolatedOneParticleSpace a) :
    lp.single (E := fun n : ℕ => bosonicHilbertSector a n) 2 1 (f.val 1)=f.val :=
  congrArg Subtype.val ((wickOneSectorIsolated a).apply_symm_apply f)

theorem wick_one_particle_projection_range (a : Parameters) :
    Set.range (wickOneParticleProjection a)=(wickIsolatedOneParticleSpace a : Set (FockHilbert a)) := by
  ext f
  constructor
  · rintro ⟨g,rfl⟩
    apply (wick_isolated_one_particle_space_iff a _).mpr
    intro n hn
    rw [wick_one_particle_projection_component,if_neg hn]
  · intro hf
    refine ⟨f,?_⟩
    have h := (wick_isolated_reconstruct a ⟨f,hf⟩)
    apply lp.ext
    funext n
    rw [wick_one_particle_projection_component]
    by_cases hn : n=1
    · rw [if_pos hn]
    · rw [if_neg hn]
      exact ((wick_isolated_one_particle_space_iff a f).mp hf n hn).symm

def wickOriginalIsolatedCore (a : Parameters) (f : bosonicSchwartz 1) :
    wickIsolatedOneParticleSpace a :=
  ⟨finiteParticleCoreToFock a (wickOneParticleCore f),
    wick_isolated_one_particle_contains_original_core a f⟩

theorem wick_wigner_isolated_original_core (a : Parameters) (f : bosonicSchwartz 1) :
    wickWignerToIsolated a (oneParticleSectorToHilbert a f)=wickOriginalIsolatedCore a f := by
  apply Subtype.ext
  change lp.single (E := fun n : ℕ => bosonicHilbertSector a n) 2 1 (wickOneSectorCoordinates a (oneParticleSectorToHilbert a f))=_
  rw [wick_one_sector_coordinates_original_core]
  exact (finiteParticleCoreToFock_on_sector a 1 f).symm

theorem wick_isolated_covariant_original_core (a : Parameters) (f : bosonicSchwartz 1) :
    wickIsolatedCovariantHilbert a (wickOriginalIsolatedCore a f)=
      wickCovariantNormalization a (oneParticleSectorToHilbert a f) := by
  rw [← wick_wigner_isolated_original_core]
  exact congrArg (wickCovariantNormalization a)
    ((wickWignerToIsolated a).symm_apply_apply (oneParticleSectorToHilbert a f))

theorem wick_isolated_original_core_dense (a : Parameters) :
    DenseRange (wickOriginalIsolatedCore a) := by
  have h := (wickWignerToIsolated a).surjective.denseRange.comp
    (oneParticleSectorToHilbert_dense a) (wickWignerToIsolated a).continuous
  simpa only [Function.comp_def,wick_wigner_isolated_original_core] using h

theorem wick_one_sector_coordinates_symm_ae (a : Parameters) (f : bosonicHilbertSector a 1) :
    (wickOneSectorCoordinates a).symm f =ᵐ[wignerMeasure a]
      (fun p => f.val (wickOneConfigurationME.symm p)) :=
  Lp.coeFn_compMeasurePreserving f.val
    (MeasurePreserving.symm wickOneConfigurationME (wick_one_configuration_measure a))

theorem wick_isolated_covariant_ae (a : Parameters) (f : wickIsolatedOneParticleSpace a) :
    wickIsolatedCovariantHilbert a f =ᵐ[wickCovariantMeasure a]
      (fun p => (wickCovariantRoot a : ℂ)*(f.val 1).val (wickOneConfigurationME.symm p)) := by
  filter_upwards [wick_covariant_forward_ae a ((wickOneSectorCoordinates a).symm (f.val 1)),
    (wick_covariant_ae a).mpr (wick_one_sector_coordinates_symm_ae a (f.val 1))] with p hp hq
  change wickCovariantForward a ((wickOneSectorCoordinates a).symm (f.val 1)) p=_
  rw [hp,hq]

theorem wick_isolated_covariant_symm_ae (a : Parameters) (f : WickCovariantHilbert a) :
    (((wickIsolatedCovariantHilbert a).symm f).val 1).val =ᵐ[particleMeasure a 1]
      (fun x => (wickCovariantRoot a : ℂ)⁻¹*f (x 0)) := by
  filter_upwards [wick_one_sector_coordinates_ae a (wickCovariantInverse a f),
    (wick_one_configuration_measure a).quasiMeasurePreserving.ae (wick_covariant_inverse_ae a f)]
      with x hx hy
  change (wickOneSectorCoordinates a (wickCovariantInverse a f)).val x=_
  rw [hx]
  exact hy

theorem wick_isolated_covariant_norm (a : Parameters) (f : wickIsolatedOneParticleSpace a) :
    ‖wickIsolatedCovariantHilbert a f‖=‖f.val‖ :=
  (wickIsolatedCovariantHilbert a).norm_map f

theorem wick_isolated_covariant_inner (a : Parameters) (f g : wickIsolatedOneParticleSpace a) :
    inner ℂ (wickIsolatedCovariantHilbert a f) (wickIsolatedCovariantHilbert a g)=inner ℂ f.val g.val :=
  (wickIsolatedCovariantHilbert a).inner_map_map (𝕜 := ℂ) f g

end AASCKleinGordon
