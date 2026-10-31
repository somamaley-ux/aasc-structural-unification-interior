import WickOneParticlePoincare

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open MeasureTheory Filter
namespace AASCKleinGordon

theorem wick_particle_four_momentum_one (a : Parameters) (x : ParticleConfiguration 1) :
    particleFourMomentum a 1 x=massShell a (x 0) := by
  simp [particleFourMomentum]

theorem wick_joint_projection_preserves_isolated (a : Parameters) (B : Set FourMomentum)
    (hB : MeasurableSet B) (f : wickIsolatedOneParticleSpace a) :
    jointSpectralProjection a B hB f.val∈wickIsolatedOneParticleSpace a := by
  apply (wick_isolated_one_particle_space_iff a _).mpr
  intro n hn
  change symbolSector a (jointCutoffSymbol a B hB) n (f.val n)=0
  rw [(wick_isolated_one_particle_space_iff a f.val).mp f.property n hn,map_zero]

def wickIsolatedJointProjection (a : Parameters) (B : Set FourMomentum) (hB : MeasurableSet B) :
    wickIsolatedOneParticleSpace a →L[ℂ] wickIsolatedOneParticleSpace a :=
  ((jointSpectralProjection a B hB).comp (wickIsolatedOneParticleSpace a).subtypeL).codRestrict
    (wickIsolatedOneParticleSpace a) (wick_joint_projection_preserves_isolated a B hB)

def wickCovariantJointProjection (a : Parameters) (B : Set FourMomentum) (hB : MeasurableSet B) :
    WickCovariantHilbert a →L[ℂ] WickCovariantHilbert a :=
  (wickIsolatedCovariantHilbert a).toLinearIsometry.toContinuousLinearMap.comp
    ((wickIsolatedJointProjection a B hB).comp
      (wickIsolatedCovariantHilbert a).symm.toLinearIsometry.toContinuousLinearMap)

theorem wick_isolated_covariant_joint_PVM_intertwining (a : Parameters) (B : Set FourMomentum)
    (hB : MeasurableSet B) (f : wickIsolatedOneParticleSpace a) :
    wickIsolatedCovariantHilbert a (wickIsolatedJointProjection a B hB f)=
      wickCovariantJointProjection a B hB (wickIsolatedCovariantHilbert a f) := by
  change _=wickIsolatedCovariantHilbert a (wickIsolatedJointProjection a B hB
    ((wickIsolatedCovariantHilbert a).symm (wickIsolatedCovariantHilbert a f)))
  exact congrArg (fun z => wickIsolatedCovariantHilbert a (wickIsolatedJointProjection a B hB z))
    ((wickIsolatedCovariantHilbert a).symm_apply_apply f).symm

theorem wick_covariant_joint_PVM_ae (a : Parameters) (B : Set FourMomentum)
    (hB : MeasurableSet B) (f : WickCovariantHilbert a) :
    wickCovariantJointProjection a B hB f =ᵐ[wickCovariantMeasure a]
      (fun p => B.indicator (fun _ => (1 : ℂ)) (massShell a p)*f p) := by
  let g := (wickIsolatedCovariantHilbert a).symm f
  have hJ := (wick_covariant_ae a).mpr
    ((MeasurePreserving.symm wickOneConfigurationME (wick_one_configuration_measure a)).quasiMeasurePreserving.ae
      (jointSpectralProjection_ae a B hB g.val 1))
  have hW := (wick_covariant_ae a).mpr
    ((MeasurePreserving.symm wickOneConfigurationME (wick_one_configuration_measure a)).quasiMeasurePreserving.ae
      (wick_isolated_covariant_symm_ae a f))
  filter_upwards [wick_isolated_covariant_ae a (wickIsolatedJointProjection a B hB g),hJ,hW]
    with p hp hq hr
  change wickIsolatedCovariantHilbert a (wickIsolatedJointProjection a B hB g) p=_
  rw [hp]
  change (wickCovariantRoot a : ℂ)*(jointSpectralProjection a B hB g.val 1).val
    (wickOneConfigurationME.symm p)=_
  rw [hq,wick_particle_four_momentum_one,hr]
  change (wickCovariantRoot a : ℂ)*(B.indicator (fun _ => (1 : ℂ)) (massShell a p)*
    ((wickCovariantRoot a : ℂ)⁻¹*f p))=_
  have hroot : (wickCovariantRoot a : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (wick_covariant_root_positive a).ne'
  field_simp

theorem wick_isolated_joint_PVM_univ (a : Parameters) :
    wickIsolatedJointProjection a Set.univ MeasurableSet.univ=
      ContinuousLinearMap.id ℂ (wickIsolatedOneParticleSpace a) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  change jointSpectralProjection a Set.univ MeasurableSet.univ f.val=f.val
  rw [jointSpectralProjection_univ]
  rfl

theorem wick_covariant_joint_PVM_univ (a : Parameters) :
    wickCovariantJointProjection a Set.univ MeasurableSet.univ=
      ContinuousLinearMap.id ℂ (WickCovariantHilbert a) := by
  apply ContinuousLinearMap.ext
  intro f
  change wickIsolatedCovariantHilbert a
    (wickIsolatedJointProjection a Set.univ MeasurableSet.univ ((wickIsolatedCovariantHilbert a).symm f))=f
  rw [wick_isolated_joint_PVM_univ]
  exact (wickIsolatedCovariantHilbert a).apply_symm_apply f

theorem wick_isolated_joint_PVM_inter (a : Parameters) (B C : Set FourMomentum)
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    (wickIsolatedJointProjection a B hB).comp (wickIsolatedJointProjection a C hC)=
      wickIsolatedJointProjection a (B∩C) (hB.inter hC) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  exact congrArg (fun e : FockHilbert a →L[ℂ] FockHilbert a => e f.val)
    (jointSpectralProjection_inter a B C hB hC)

theorem wick_covariant_joint_PVM_inter (a : Parameters) (B C : Set FourMomentum)
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    (wickCovariantJointProjection a B hB).comp (wickCovariantJointProjection a C hC)=
      wickCovariantJointProjection a (B∩C) (hB.inter hC) := by
  apply ContinuousLinearMap.ext
  intro f
  change wickIsolatedCovariantHilbert a (wickIsolatedJointProjection a B hB
    ((wickIsolatedCovariantHilbert a).symm (wickIsolatedCovariantHilbert a
      (wickIsolatedJointProjection a C hC ((wickIsolatedCovariantHilbert a).symm f)))))=_
  exact (congrArg (fun z => wickIsolatedCovariantHilbert a (wickIsolatedJointProjection a B hB z))
    ((wickIsolatedCovariantHilbert a).symm_apply_apply
      (wickIsolatedJointProjection a C hC ((wickIsolatedCovariantHilbert a).symm f)))).trans
    (congrArg (wickIsolatedCovariantHilbert a)
      (congrArg (fun e : wickIsolatedOneParticleSpace a →L[ℂ] wickIsolatedOneParticleSpace a =>
        e ((wickIsolatedCovariantHilbert a).symm f)) (wick_isolated_joint_PVM_inter a B C hB hC)))

theorem wick_covariant_joint_PVM_one_mass_window (a : Parameters) :
    wickCovariantJointProjection a (wickOneMassWindow a) (wick_one_mass_window_measurable a)=
      ContinuousLinearMap.id ℂ (WickCovariantHilbert a) := by
  apply ContinuousLinearMap.ext
  intro f
  have hg := ((wickIsolatedCovariantHilbert a).symm f).property
  have hfix : wickOneParticleProjection a ((wickIsolatedCovariantHilbert a).symm f).val=
      ((wickIsolatedCovariantHilbert a).symm f).val := by
    change (wickOneParticleProjection a-ContinuousLinearMap.id ℂ (FockHilbert a)) _=0 at hg
    simpa only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,sub_eq_zero] using hg
  have hJ : wickIsolatedJointProjection a (wickOneMassWindow a) (wick_one_mass_window_measurable a)
      ((wickIsolatedCovariantHilbert a).symm f)=(wickIsolatedCovariantHilbert a).symm f := by
    apply Subtype.ext
    exact (congrArg (fun e => e ((wickIsolatedCovariantHilbert a).symm f).val)
      (wick_joint_mass_window_is_one_particle a)).trans hfix
  change wickIsolatedCovariantHilbert a
    (wickIsolatedJointProjection a (wickOneMassWindow a) (wick_one_mass_window_measurable a)
      ((wickIsolatedCovariantHilbert a).symm f))=f
  exact (congrArg (wickIsolatedCovariantHilbert a) hJ).trans
    ((wickIsolatedCovariantHilbert a).apply_symm_apply f)

end AASCKleinGordon
