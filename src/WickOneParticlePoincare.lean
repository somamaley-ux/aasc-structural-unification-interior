import WickIsolatedCovariantHilbert
import KGGeneralPoincareRepresentation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open MeasureTheory Filter
namespace AASCKleinGordon

theorem wick_original_poincare_component (a : Parameters) (q : ProperPoincareTransform)
    (f : FockHilbert a) (n : ℕ) :
    originalFockPoincareRepresentation a q f n=
      bosonicPhaseMultiplier a n (particleEventMomentum a n q.left.toAdd)
        (particleEventMomentum_continuous a n q.left.toAdd).measurable
        (particleEventMomentum_permutation a n q.left.toAdd) a.hbar 1
        (bosonicLorentzUnitary a n q.right (f n)) := rfl

theorem wick_original_poincare_preserves_isolated (a : Parameters) (q : ProperPoincareTransform)
    (f : wickIsolatedOneParticleSpace a) :
    originalFockPoincareRepresentation a q f.val∈wickIsolatedOneParticleSpace a := by
  apply (wick_isolated_one_particle_space_iff a _).mpr
  intro n hn
  rw [wick_original_poincare_component,
    (wick_isolated_one_particle_space_iff a f.val).mp f.property n hn,map_zero,map_zero]

def wickIsolatedPoincareUnitary (a : Parameters) (q : ProperPoincareTransform) :
    wickIsolatedOneParticleSpace a ≃ₗᵢ[ℂ] wickIsolatedOneParticleSpace a where
  toFun f := ⟨originalFockPoincareRepresentation a q f.val,wick_original_poincare_preserves_isolated a q f⟩
  invFun f := ⟨originalFockPoincareRepresentation a q⁻¹ f.val,wick_original_poincare_preserves_isolated a q⁻¹ f⟩
  left_inv f := by
    apply Subtype.ext
    change originalFockPoincareRepresentation a q⁻¹ (originalFockPoincareRepresentation a q f.val)=f.val
    simpa only [map_inv] using (originalFockPoincareRepresentation a q).symm_apply_apply f.val
  right_inv f := by
    apply Subtype.ext
    change originalFockPoincareRepresentation a q (originalFockPoincareRepresentation a q⁻¹ f.val)=f.val
    simpa only [map_inv] using (originalFockPoincareRepresentation a q).apply_symm_apply f.val
  map_add' f g := Subtype.ext ((originalFockPoincareRepresentation a q).map_add f.val g.val)
  map_smul' c f := Subtype.ext ((originalFockPoincareRepresentation a q).map_smul c f.val)
  norm_map' f := (originalFockPoincareRepresentation a q).norm_map f.val

def wickIsolatedPoincareRepresentation (a : Parameters) :
    ProperPoincareTransform →* (wickIsolatedOneParticleSpace a ≃ₗᵢ[ℂ] wickIsolatedOneParticleSpace a) where
  toFun := wickIsolatedPoincareUnitary a
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro f
    apply Subtype.ext
    change originalFockPoincareRepresentation a 1 f.val=f.val
    rw [map_one]
    rfl
  map_mul' q r := by
    apply LinearIsometryEquiv.ext
    intro f
    apply Subtype.ext
    exact congrArg (fun e : FockHilbert a ≃ₗᵢ[ℂ] FockHilbert a => e f.val)
      ((originalFockPoincareRepresentation a).map_mul q r)

/-- Algebraic transport is proved with abstract carriers so rewriting does not
unfold the concrete Lp normalization while checking the representation law. -/
def wickTransportUnitaryRepresentation {G E F : Type*} [Group G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (u : E ≃ₗᵢ[ℂ] F) (ρ : G →* (E ≃ₗᵢ[ℂ] E)) : G →* (F ≃ₗᵢ[ℂ] F) where
  toFun q := (u.symm.trans (ρ q)).trans u
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro f
    change u (ρ 1 (u.symm f))=f
    rw [ρ.map_one]
    exact u.apply_symm_apply f
  map_mul' q r := by
    apply LinearIsometryEquiv.ext
    intro f
    change u (ρ (q*r) (u.symm f))=u (ρ q (u.symm (u (ρ r (u.symm f)))))
    rw [u.symm_apply_apply]
    exact congrArg u (congrArg (fun e : E ≃ₗᵢ[ℂ] E => e (u.symm f)) (ρ.map_mul q r))

def wickCovariantPoincareRepresentation (a : Parameters) :
    ProperPoincareTransform →* (WickCovariantHilbert a ≃ₗᵢ[ℂ] WickCovariantHilbert a) :=
  wickTransportUnitaryRepresentation (wickIsolatedCovariantHilbert a) (wickIsolatedPoincareRepresentation a)

theorem wick_isolated_covariant_poincare_intertwining (a : Parameters) (q : ProperPoincareTransform)
    (f : wickIsolatedOneParticleSpace a) :
    wickIsolatedCovariantHilbert a (wickIsolatedPoincareRepresentation a q f)=
      wickCovariantPoincareRepresentation a q (wickIsolatedCovariantHilbert a f) := by
  change _=wickIsolatedCovariantHilbert a (wickIsolatedPoincareRepresentation a q
    ((wickIsolatedCovariantHilbert a).symm (wickIsolatedCovariantHilbert a f)))
  exact congrArg (fun z => wickIsolatedCovariantHilbert a (wickIsolatedPoincareRepresentation a q z))
    ((wickIsolatedCovariantHilbert a).symm_apply_apply f).symm

theorem wick_isolated_poincare_strongly_continuous (a : Parameters) (f : wickIsolatedOneParticleSpace a) :
    Continuous (fun q => wickIsolatedPoincareRepresentation a q f) :=
  (originalFockPoincareRepresentation_strongly_continuous a f.val).subtype_mk _

theorem wick_covariant_poincare_strongly_continuous (a : Parameters) (f : WickCovariantHilbert a) :
    Continuous (fun q => wickCovariantPoincareRepresentation a q f) :=
  (wickIsolatedCovariantHilbert a).continuous.comp
    (wick_isolated_poincare_strongly_continuous a ((wickIsolatedCovariantHilbert a).symm f))

theorem wick_original_poincare_one_ae (a : Parameters) (q : ProperPoincareTransform)
    (f : FockHilbert a) :
    (originalFockPoincareRepresentation a q f 1).val =ᵐ[particleMeasure a 1]
      (fun x => Translation.phase a.hbar 1 (eventMomentumPair a q.left.toAdd (x 0))*
        (f 1).val (fun i => lorentzShellMap a q.right⁻¹ (x i))) := by
  filter_upwards [particleLorentzUnitary_ae a 1 q.right (f 1).val,
    Multiplication.phaseMultiplier_ae (particleEventMomentum a 1 q.left.toAdd)
      (particleEventMomentum_continuous a 1 q.left.toAdd).measurable a.hbar 1
      (particleLorentzUnitary a 1 q.right (f 1).val)] with x hx hy
  change (Multiplication.phaseMultiplier (particleEventMomentum a 1 q.left.toAdd)
    (particleEventMomentum_continuous a 1 q.left.toAdd).measurable a.hbar 1
    (particleLorentzUnitary a 1 q.right (f 1).val)) x=_
  rw [hy,hx]
  simp only [particleEventMomentum,Fin.sum_univ_one]

theorem wick_covariant_poincare_scalar_ae (a : Parameters) (q : ProperPoincareTransform)
    (f : WickCovariantHilbert a) :
    wickCovariantPoincareRepresentation a q f =ᵐ[wickCovariantMeasure a]
      (fun p => Translation.phase a.hbar 1 (eventMomentumPair a q.left.toAdd p)*
        f (lorentzShellMap a q.right⁻¹ p)) := by
  let g := (wickIsolatedCovariantHilbert a).symm f
  have hU := wick_original_poincare_one_ae a q g.val
  have hF := (wick_covariant_ae a).mpr
    ((MeasurePreserving.symm wickOneConfigurationME (wick_one_configuration_measure a)).quasiMeasurePreserving.ae hU)
  have hL := (particleLorentz_preserves_measure a 1 q.right⁻¹).quasiMeasurePreserving.ae
    (wick_isolated_covariant_symm_ae a f)
  have hW := (wick_covariant_ae a).mpr
    ((MeasurePreserving.symm wickOneConfigurationME (wick_one_configuration_measure a)).quasiMeasurePreserving.ae hL)
  filter_upwards [wick_isolated_covariant_ae a (wickIsolatedPoincareRepresentation a q g),hF,hW]
    with p hp hq hr
  change wickIsolatedCovariantHilbert a (wickIsolatedPoincareRepresentation a q g) p=_
  rw [hp]
  change (wickCovariantRoot a : ℂ)*(originalFockPoincareRepresentation a q g.val 1).val
    (wickOneConfigurationME.symm p)=_
  rw [hq]
  change (wickCovariantRoot a : ℂ)*(Translation.phase a.hbar 1 (eventMomentumPair a q.left.toAdd p)*
    (g.val 1).val (particleLorentzME a 1 q.right⁻¹ (wickOneConfigurationME.symm p)))=_
  rw [hr]
  change (wickCovariantRoot a : ℂ)*(Translation.phase a.hbar 1 (eventMomentumPair a q.left.toAdd p)*
    ((wickCovariantRoot a : ℂ)⁻¹*f (lorentzShellMap a q.right⁻¹ p)))=_
  have hroot : (wickCovariantRoot a : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (wick_covariant_root_positive a).ne'
  field_simp

end AASCKleinGordon
