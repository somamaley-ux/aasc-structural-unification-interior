import KGGeneralPoincareContinuity
import KGGeneralPoincareLocalCovariance
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.Equiv.TypeTags

noncomputable section
set_option maxHeartbeats 1800000
namespace AASCKleinGordon

def lorentzTranslationAutomorphism : ProperLorentzTransform →* MulAut (Multiplicative Spacetime) where
  toFun L:=AddEquiv.toMultiplicative (spacetimeLorentzCLE L).toLinearEquiv.toAddEquiv
  map_one' := by
    apply MulEquiv.ext
    intro b
    exact congrArg Multiplicative.ofAdd (spacetimeLorentz_one b.toAdd)
  map_mul' L M:=by
    apply MulEquiv.ext
    intro b
    exact congrArg Multiplicative.ofAdd (spacetimeLorentz_mul L M b.toAdd)

abbrev ProperPoincareTransform :=
  Multiplicative Spacetime ⋊[lorentzTranslationAutomorphism] ProperLorentzTransform

def poincareCoordinates (q : ProperPoincareTransform) : Spacetime × ProperLorentzTransform :=
  (q.left.toAdd,q.right)

instance properPoincareTopologicalSpace : TopologicalSpace ProperPoincareTransform :=
  TopologicalSpace.induced poincareCoordinates inferInstance

theorem poincareCoordinates_isInducing : Topology.IsInducing poincareCoordinates := ⟨rfl⟩

theorem poincareCoordinates_continuous : Continuous poincareCoordinates := continuous_induced_dom

theorem poincareCoordinates_mul (q r : ProperPoincareTransform) :
    poincareCoordinates (q*r)=
      (q.left.toAdd+spacetimeLorentzCLE q.right r.left.toAdd,q.right*r.right) := rfl

theorem poincareCoordinates_inverse (q : ProperPoincareTransform) :
    poincareCoordinates q⁻¹=(spacetimeLorentzCLE q.right⁻¹ (-q.left.toAdd),q.right⁻¹) := rfl

instance properPoincareTopologicalGroup : IsTopologicalGroup ProperPoincareTransform where
  continuous_mul := by
    apply poincareCoordinates_isInducing.continuous_iff.mpr
    change Continuous (fun p : ProperPoincareTransform × ProperPoincareTransform =>
      (p.1.left.toAdd+spacetimeLorentzCLE p.1.right p.2.left.toAdd,p.1.right*p.2.right))
    exact ((poincareCoordinates_continuous.fst.comp continuous_fst).add
      (spacetimeLorentz_jointly_continuous.comp
        ((poincareCoordinates_continuous.snd.comp continuous_fst).prodMk
          (poincareCoordinates_continuous.fst.comp continuous_snd)))).prodMk
      ((poincareCoordinates_continuous.snd.comp continuous_fst).mul
        (poincareCoordinates_continuous.snd.comp continuous_snd))
  continuous_inv := by
    apply poincareCoordinates_isInducing.continuous_iff.mpr
    change Continuous (fun q : ProperPoincareTransform =>
      (spacetimeLorentzCLE q.right⁻¹ (-q.left.toAdd),q.right⁻¹))
    exact (spacetimeLorentz_jointly_continuous.comp
      (poincareCoordinates_continuous.snd.inv.prodMk poincareCoordinates_continuous.fst.neg)).prodMk
      poincareCoordinates_continuous.snd.inv

def originalFockPoincareRepresentation (a : Parameters) :
    ProperPoincareTransform →* (FockHilbert a ≃ₗᵢ[ℂ] FockHilbert a) where
  toFun q:=fockPoincareUnitary a q.left.toAdd q.right
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro f
    exact fockPoincareUnitary_one a f
  map_mul' q r:=by
    apply LinearIsometryEquiv.ext
    intro f
    exact (fockPoincareUnitary_mul a q.left.toAdd r.left.toAdd q.right r.right f).symm

theorem originalFockPoincareRepresentation_strongly_continuous (a : Parameters) (f : FockHilbert a) :
    Continuous (fun q : ProperPoincareTransform => originalFockPoincareRepresentation a q f) := by
  change Continuous (fun q : ProperPoincareTransform => fockPoincareUnitary a q.left.toAdd q.right f)
  have h := (fockPoincare_strongly_continuous a f).comp poincareCoordinates_continuous
  exact h

theorem originalFockPoincareRepresentation_jointly_continuous (a : Parameters) :
    Continuous (fun p : ProperPoincareTransform × FockHilbert a =>
      originalFockPoincareRepresentation a p.1 p.2) := by
  change Continuous (fun p : ProperPoincareTransform × FockHilbert a =>
    fockPoincareUnitary a p.1.left.toAdd p.1.right p.2)
  let Φ : ProperPoincareTransform × FockHilbert a →
      (Spacetime × ProperLorentzTransform) × FockHilbert a :=
    fun p => (poincareCoordinates p.1,p.2)
  have hΦ : Continuous Φ :=
    (poincareCoordinates_continuous.comp continuous_fst).prodMk continuous_snd
  have h := (fockPoincare_jointly_continuous a).comp hΦ
  exact h

theorem originalFockPoincareRepresentation_preserves_domain (a : Parameters)
    (q : ProperPoincareTransform) (v : fockCoreDomain a) :
    originalFockPoincareRepresentation a q v.val ∈ fockCoreDomain a := by
  obtain ⟨u,hu⟩:=v.property
  rw [← hu]
  change fockPoincareUnitary a q.left.toAdd q.right (finiteParticleCoreToFock a u)∈_
  rw [fockPoincare_intertwines_original_core]
  exact ⟨corePoincare a q.left.toAdd q.right u,rfl⟩

theorem originalFockPoincareRepresentation_field (a : Parameters) (q : ProperPoincareTransform)
    (s : ℝ) (h : SchwartzMap Spacetime ℂ) (u : FiniteParticleCore) :
    originalFockPoincareRepresentation a q (fockSpacetimeField a s h (includedFockCore a u))=
      fockSpacetimeField a s (spacetimePoincareTestCLM q.left.toAdd q.right h)
        (includedFockCore a (corePoincare a q.left.toAdd q.right u)) := by
  change fockPoincareUnitary a q.left.toAdd q.right
    (fockSpacetimeField a s h (includedFockCore a u))=_
  rw [fockSpacetimeField_on_original_core,fockPoincare_intertwines_original_core,
    spacetimeFieldCore_poincare,fockSpacetimeField_on_original_core]
  rfl

theorem originalFockPoincareRepresentation_vacuum (a : Parameters) (q : ProperPoincareTransform) :
    originalFockPoincareRepresentation a q (fockVacuum a)=fockVacuum a :=
  fockPoincareUnitary_fixes_vacuum a q.left.toAdd q.right

end AASCKleinGordon
