import KGGeneralPoincareCovariance
import KGGeneralLocalFieldCovariance

noncomputable section
set_option maxHeartbeats 1800000
open Set
open scoped SchwartzMap
namespace AASCKleinGordon

def spacetimePoincareTestCLM (b : Spacetime) (L : ProperLorentzTransform) :
    𝓢(Spacetime,ℂ) →L[ℂ] 𝓢(Spacetime,ℂ) :=
  (spacetimeEventTranslationTestCLM b).comp (spacetimeLorentzTestCLM L)

def poincareTransformedRegion (b : Spacetime) (L : ProperLorentzTransform)
    (O : Set Spacetime) : Set Spacetime :=
  eventTranslatedRegion b (lorentzTransformedRegion L O)

theorem poincareTransformedRegion_eq_affine_image (b : Spacetime) (L : ProperLorentzTransform)
    (O : Set Spacetime) : poincareTransformedRegion b L O=(fun x => b+spacetimeLorentzCLE L x) '' O := by
  simp only [poincareTransformedRegion,eventTranslatedRegion,lorentzTransformedRegion,
    Set.image_image,Function.comp_def,add_comm]

theorem spacetimePoincare_tsupport (b : Spacetime) (L : ProperLorentzTransform)
    (h : 𝓢(Spacetime,ℂ)) :
    tsupport (spacetimePoincareTestCLM b L h : Spacetime → ℂ)=
      poincareTransformedRegion b L (tsupport (h : Spacetime → ℂ)) := by
  change tsupport (spacetimeEventTranslationTestCLM b (spacetimeLorentzTestCLM L h) : Spacetime → ℂ)=_
  rw [spacetimeEventTranslation_tsupport,spacetimeLorentz_tsupport]
  rfl

theorem spacetimePoincare_compact_support (b : Spacetime) (L : ProperLorentzTransform)
    (h : 𝓢(Spacetime,ℂ)) (hc : HasCompactSupport (h : Spacetime → ℂ)) :
    HasCompactSupport (spacetimePoincareTestCLM b L h : Spacetime → ℂ) :=
  spacetimeEventTranslation_compact_support b _ (spacetimeLorentz_compact_support L h hc)

theorem spacelikeSeparatedTests_poincare (b : Spacetime) (L : ProperLorentzTransform)
    (h k : 𝓢(Spacetime,ℂ)) (hs : SpacelikeSeparatedTests h k) :
    SpacelikeSeparatedTests (spacetimePoincareTestCLM b L h) (spacetimePoincareTestCLM b L k) :=
  spacelikeSeparatedTests_eventTranslation b _ _ (spacelikeSeparatedTests_lorentz L h k hs)

def corePoincareEquiv (a : Parameters) (b : Spacetime) (L : ProperLorentzTransform) :
    FiniteParticleCore ≃ₗ[ℂ] FiniteParticleCore :=
  (coreLorentzEquiv a L).toLinearEquiv.trans (coreEventTranslationEquiv a b)

def originalPoincareFieldConjugation (a : Parameters) (b : Spacetime) (L : ProperLorentzTransform) :
    Module.End ℂ FiniteParticleCore ≃ₐ[ℂ] Module.End ℂ FiniteParticleCore :=
  (corePoincareEquiv a b L).conjAlgEquiv ℂ

theorem originalPoincareFieldConjugation_field (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (h : 𝓢(Spacetime,ℂ)) :
    originalPoincareFieldConjugation a b L (spacetimeFieldCore a s h)=
      spacetimeFieldCore a s (spacetimePoincareTestCLM b L h) := by
  apply LinearMap.ext
  intro u
  change corePoincare a b L (spacetimeFieldCore a s h ((corePoincareEquiv a b L).symm u))=_
  rw [spacetimeFieldCore_poincare]
  change spacetimeFieldCore a s (spacetimePoincareTestCLM b L h)
    ((corePoincareEquiv a b L) ((corePoincareEquiv a b L).symm u))=_
  rw [LinearEquiv.apply_symm_apply]

theorem originalPoincareFieldConjugation_generators (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (O : Set Spacetime) :
    originalPoincareFieldConjugation a b L '' originalLocalFieldGenerators a s O=
      originalLocalFieldGenerators a s (poincareTransformedRegion b L O) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨A,⟨h,hc,hs,rfl⟩,rfl⟩
    refine ⟨spacetimePoincareTestCLM b L h,spacetimePoincare_compact_support b L h hc,?_,
      originalPoincareFieldConjugation_field a b L s h⟩
    rw [spacetimePoincare_tsupport]
    exact Set.image_mono (Set.image_mono hs)
  · rintro B ⟨k,kc,ks,rfl⟩
    let h:=spacetimeLorentzTestCLM L⁻¹ (spacetimeEventTranslationTestCLM (-b) k)
    have hh : spacetimePoincareTestCLM b L h=k := by
      change spacetimeEventTranslationTestCLM b
        (spacetimeLorentzTestCLM L (spacetimeLorentzTestCLM L⁻¹
          (spacetimeEventTranslationTestCLM (-b) k)))=k
      rw [spacetimeLorentzTest_mul,mul_inv_cancel,spacetimeLorentzTest_one,
        spacetimeEventTranslationTest_add,add_neg_cancel,spacetimeEventTranslationTest_zero]
    refine ⟨spacetimeFieldCore a s h,⟨h,
      spacetimeLorentz_compact_support L⁻¹ _ (spacetimeEventTranslation_compact_support (-b) k kc),?_,rfl⟩,?_⟩
    · intro x hx
      change x∈tsupport (spacetimeLorentzTestCLM L⁻¹
        (spacetimeEventTranslationTestCLM (-b) k) : Spacetime → ℂ) at hx
      rw [spacetimeLorentz_tsupport] at hx
      obtain ⟨y,hy,rfl⟩ := hx
      rw [spacetimeEventTranslation_tsupport] at hy
      obtain ⟨z,hz,rfl⟩ := hy
      obtain ⟨v,hv,rfl⟩ := ks hz
      obtain ⟨w,hw,rfl⟩ := hv
      simpa only [add_neg_cancel_right,spacetimeLorentz_inverse] using hw
    · rw [originalPoincareFieldConjugation_field,hh]

theorem originalLocalFieldAlgebra_poincare (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (O : Set Spacetime) :
    (originalLocalFieldAlgebra a s O).map (originalPoincareFieldConjugation a b L).toAlgHom=
      originalLocalFieldAlgebra a s (poincareTransformedRegion b L O) := by
  unfold originalLocalFieldAlgebra
  rw [AlgHom.map_adjoin]
  congr 1
  exact originalPoincareFieldConjugation_generators a b L s O

end AASCKleinGordon
