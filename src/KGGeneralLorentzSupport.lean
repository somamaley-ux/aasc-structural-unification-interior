import KGGeneralLorentzFieldCovariance
import KGEventTranslationSupport

noncomputable section
set_option maxHeartbeats 1400000
open Set
open scoped SchwartzMap
namespace AASCKleinGordon

def lorentzTransformedRegion (L : ProperLorentzTransform) (O : Set Spacetime) : Set Spacetime :=
  spacetimeLorentzCLE L '' O

theorem spacetimeLorentz_tsupport_preimage (L : ProperLorentzTransform) (h : 𝓢(Spacetime,ℂ)) :
    tsupport (spacetimeLorentzTestCLM L h : Spacetime → ℂ) ⊆
      {x : Spacetime | spacetimeLorentzCLE L⁻¹ x ∈ tsupport (h : Spacetime → ℂ)} := by
  apply closure_minimal
  · intro x hx
    change h (spacetimeLorentzCLE L⁻¹ x) ≠ 0 at hx
    exact subset_tsupport h hx
  · exact isClosed_closure.preimage (spacetimeLorentzCLE L⁻¹).continuous

theorem spacetimeLorentz_tsupport (L : ProperLorentzTransform) (h : 𝓢(Spacetime,ℂ)) :
    tsupport (spacetimeLorentzTestCLM L h : Spacetime → ℂ)=
      lorentzTransformedRegion L (tsupport (h : Spacetime → ℂ)) := by
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨spacetimeLorentzCLE L⁻¹ x,spacetimeLorentz_tsupport_preimage L h hx,?_⟩
    simpa only [inv_inv] using spacetimeLorentz_inverse L⁻¹ x
  · rintro _ ⟨y,hy,rfl⟩
    have hinv : spacetimeLorentzTestCLM L⁻¹ (spacetimeLorentzTestCLM L h)=h := by
      rw [spacetimeLorentzTest_mul,inv_mul_cancel,spacetimeLorentzTest_one]
    have hy' : y ∈ tsupport
        (spacetimeLorentzTestCLM L⁻¹ (spacetimeLorentzTestCLM L h) : Spacetime → ℂ) := by
      rw [hinv]
      exact hy
    simpa only [inv_inv] using
      spacetimeLorentz_tsupport_preimage L⁻¹ (spacetimeLorentzTestCLM L h) hy'

theorem spacetimeLorentz_compact_support (L : ProperLorentzTransform) (h : 𝓢(Spacetime,ℂ))
    (hc : HasCompactSupport (h : Spacetime → ℂ)) :
    HasCompactSupport (spacetimeLorentzTestCLM L h : Spacetime → ℂ) := by
  change IsCompact (tsupport (spacetimeLorentzTestCLM L h : Spacetime → ℂ))
  rw [spacetimeLorentz_tsupport]
  exact hc.isCompact.image (spacetimeLorentzCLE L).continuous

theorem spacetimeLorentz_minkowskiSquare (L : ProperLorentzTransform) (x : Spacetime) :
    spacetimeMinkowskiSquare (spacetimeLorentzCLE L x)=spacetimeMinkowskiSquare x :=
  properLorentz_metric L (fun i => x i) (fun i => x i)

theorem spacelikeSeparatedTests_lorentz (L : ProperLorentzTransform) (h k : 𝓢(Spacetime,ℂ))
    (hs : SpacelikeSeparatedTests h k) :
    SpacelikeSeparatedTests (spacetimeLorentzTestCLM L h) (spacetimeLorentzTestCLM L k) := by
  intro x hx y hy
  rw [spacetimeLorentz_tsupport] at hx hy
  obtain ⟨x',hx',rfl⟩ := hx
  obtain ⟨y',hy',rfl⟩ := hy
  rw [← map_sub,spacetimeLorentz_minkowskiSquare]
  exact hs x' hx' y' hy'

end AASCKleinGordon
