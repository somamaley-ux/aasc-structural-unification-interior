import KGOriginalPairAdjointness
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.FDeriv.Star

/-! Actual continuous-function test separation. No pointwise adjoint identity
is received. Conjugation commutes with the actual Bochner integral. -/
noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory
open scoped SchwartzMap ComplexConjugate
namespace AASCKleinGordon
open SchwartzOperations

theorem wick_continuous_eq_of_schwartz_tests (F G : Spacetime → ℂ)
    (hF : Continuous F) (hG : Continuous G)
    (tests : ∀ h : 𝓢(Spacetime,ℂ), (∫ x,h x*F x) = ∫ x,h x*G x) : F=G := by
  apply Measure.eq_of_ae_eq (μ:=volume) ?_ hF hG
  apply ae_eq_of_integral_contDiff_smul_eq hF.locallyIntegrable hG.locallyIntegrable
  intro g hg hc
  let h : 𝓢(Spacetime,ℂ) := (hc.comp_left rfl).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hg)
  have htest := tests h
  change (∫ x,(g x : ℂ)*F x) = ∫ x,(g x : ℂ)*G x at htest
  simpa only [Complex.real_smul] using htest

theorem wick_conjugate_test_integral (F : Spacetime → ℂ) (h : 𝓢(Spacetime,ℂ)) :
    (∫ x,h x*star (F x))=star (∫ x,conjugateSchwartzCLM h x*F x) := by
  change _ = conj (∫ x,conj (h x)*F x)
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by simp)

theorem wick_bilocal_eq_of_product_schwartz_tests (F G : Spacetime → Spacetime → ℂ)
    (rightF : ∀ x,Continuous (F x)) (rightG : ∀ x,Continuous (G x))
    (smearF : ∀ k : 𝓢(Spacetime,ℂ),Continuous (fun x => ∫ y,k y*F x y))
    (smearG : ∀ k : 𝓢(Spacetime,ℂ),Continuous (fun x => ∫ y,k y*G x y))
    (tests : ∀ h k : 𝓢(Spacetime,ℂ),
      (∫ x,h x*∫ y,k y*F x y)=∫ x,h x*∫ y,k y*G x y) : F=G := by
  have outer (k : 𝓢(Spacetime,ℂ)) :=
    wick_continuous_eq_of_schwartz_tests _ _ (smearF k) (smearG k) (fun h => tests h k)
  funext x
  exact wick_continuous_eq_of_schwartz_tests _ _ (rightF x) (rightG x)
    (fun k => congrFun (outer k) x)

end AASCKleinGordon
