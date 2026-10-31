import KGJointTranslationSpectralAttachment

noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
namespace AASCKleinGordon

theorem particleFourMomentum_ne_zero_of_positive_sector (a : Parameters) (n : ℕ)
    (hn : n≠0) (x : ParticleConfiguration n) : particleFourMomentum a n x≠0 := by
  intro hz
  have hh:=congrArg (fun q : FourMomentum => q 0) hz
  change particleFourMomentum a n x 0=0 at hh
  rw [particleFourMomentum_time] at hh
  have hp:=div_pos (particleTotalEnergy_pos_of_nonzero a n hn x) a.speed_pos
  exact hp.ne' hh

theorem jointZeroProjection_zero_sector (a : Parameters) (f : FockHilbert a) :
    jointSpectralProjection a {0} (measurableSet_singleton 0) f 0=f 0 := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [jointSpectralProjection_ae a {0} (measurableSet_singleton 0) f 0] with x hx
  simpa [particleFourMomentum_zero] using hx

theorem jointZeroProjection_positive_sector (a : Parameters) (f : FockHilbert a)
    (n : ℕ) (hn : n≠0) : jointSpectralProjection a {0} (measurableSet_singleton 0) f n=0 := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [jointSpectralProjection_ae a {0} (measurableSet_singleton 0) f n,
    Lp.coeFn_zero ℂ 2 (particleMeasure a n)] with x hx hz
  have hm:particleFourMomentum a n x∉({0} : Set FourMomentum) :=
    fun hh => particleFourMomentum_ne_zero_of_positive_sector a n hn x (Set.mem_singleton_iff.mp hh)
  have he : (jointSpectralProjection a {0} (measurableSet_singleton 0) f n).val x=0 := by
    simpa only [Set.indicator_of_notMem hm,zero_mul] using hx
  exact he.trans hz.symm

theorem jointZeroProjection_range_vacuum (a : Parameters) (f : FockHilbert a) :
    ∃ z : ℂ,jointSpectralProjection a {0} (measurableSet_singleton 0) f=z • fockVacuum a :=
  fock_supported_zero_sector_is_vacuum_multiple a _ (jointZeroProjection_positive_sector a f)

theorem jointZeroProjection_fixes_vacuum (a : Parameters) :
    jointSpectralProjection a {0} (measurableSet_singleton 0) (fockVacuum a)=fockVacuum a := by
  apply lp.ext
  funext n
  cases n with
  | zero => exact jointZeroProjection_zero_sector a (fockVacuum a)
  | succ n =>
    rw [jointZeroProjection_positive_sector a _ (n+1) (Nat.succ_ne_zero n)]
    rw [fockVacuum,vacuumCore,finiteParticleCoreToFock_on_sector]
    simp [lp.single_apply]

theorem jointZeroProjection_range_eq_vacuum_line (a : Parameters) :
    Set.range (jointSpectralProjection a {0} (measurableSet_singleton 0))=
      Set.range (fun z : ℂ => z • fockVacuum a) := by
  ext f
  constructor
  · rintro ⟨u,rfl⟩
    obtain ⟨z,hz⟩:=jointZeroProjection_range_vacuum a u
    exact ⟨z,hz.symm⟩
  · rintro ⟨z,rfl⟩
    refine ⟨z • fockVacuum a,?_⟩
    rw [map_smul,jointZeroProjection_fixes_vacuum]

end AASCKleinGordon
