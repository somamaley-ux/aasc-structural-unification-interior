import KGGeneralLorentzSupport
import Mathlib.Algebra.Algebra.Equiv

noncomputable section
set_option maxHeartbeats 1600000
open Set
open scoped SchwartzMap
namespace AASCKleinGordon

def originalLorentzFieldConjugation (a : Parameters) (L : ProperLorentzTransform) :
    Module.End ℂ FiniteParticleCore ≃ₐ[ℂ] Module.End ℂ FiniteParticleCore :=
  (coreLorentzEquiv a L).conjAlgEquiv ℂ

theorem originalLorentzFieldConjugation_field (a : Parameters) (L : ProperLorentzTransform)
    (s : ℝ) (h : 𝓢(Spacetime,ℂ)) :
    originalLorentzFieldConjugation a L (spacetimeFieldCore a s h)=
      spacetimeFieldCore a s (spacetimeLorentzTestCLM L h) := by
  apply LinearMap.ext
  intro u
  change coreLorentz a L (spacetimeFieldCore a s h (coreLorentz a L⁻¹ u))=_
  rw [spacetimeFieldCore_lorentz,coreLorentz_mul,mul_inv_cancel,coreLorentz_one]

theorem originalLorentzFieldConjugation_generators (a : Parameters) (L : ProperLorentzTransform)
    (s : ℝ) (O : Set Spacetime) :
    originalLorentzFieldConjugation a L '' originalLocalFieldGenerators a s O=
      originalLocalFieldGenerators a s (lorentzTransformedRegion L O) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨A,⟨h,hc,hs,rfl⟩,rfl⟩
    refine ⟨spacetimeLorentzTestCLM L h,spacetimeLorentz_compact_support L h hc,?_,
      originalLorentzFieldConjugation_field a L s h⟩
    rw [spacetimeLorentz_tsupport]
    exact Set.image_mono hs
  · rintro B ⟨k,kc,ks,rfl⟩
    let h:=spacetimeLorentzTestCLM L⁻¹ k
    have hh : spacetimeLorentzTestCLM L h=k := by
      dsimp only [h]
      rw [spacetimeLorentzTest_mul,mul_inv_cancel,spacetimeLorentzTest_one]
    refine ⟨spacetimeFieldCore a s h,⟨h,spacetimeLorentz_compact_support L⁻¹ k kc,?_,rfl⟩,?_⟩
    · intro x hx
      change x∈tsupport (spacetimeLorentzTestCLM L⁻¹ k : Spacetime → ℂ) at hx
      rw [spacetimeLorentz_tsupport] at hx
      obtain ⟨y,hy,rfl⟩ := hx
      obtain ⟨z,hz,rfl⟩ := ks hy
      simpa only [spacetimeLorentz_inverse] using hz
    · rw [originalLorentzFieldConjugation_field,hh]

theorem originalLocalFieldAlgebra_lorentz (a : Parameters) (L : ProperLorentzTransform)
    (s : ℝ) (O : Set Spacetime) :
    (originalLocalFieldAlgebra a s O).map (originalLorentzFieldConjugation a L).toAlgHom=
      originalLocalFieldAlgebra a s (lorentzTransformedRegion L O) := by
  unfold originalLocalFieldAlgebra
  rw [AlgHom.map_adjoin]
  congr 1
  exact originalLorentzFieldConjugation_generators a L s O

end AASCKleinGordon
