import KGSpacetimeEventTranslationTests
import KGOriginalLocalFieldAlgebras

noncomputable section
set_option maxHeartbeats 1400000
open Set
open scoped SchwartzMap
namespace AASCKleinGordon

def eventTranslatedRegion (b : Spacetime) (O : Set Spacetime) : Set Spacetime :=
  (fun x => x+b) '' O

theorem spacetimeEventTranslation_tsupport_preimage (b : Spacetime) (h : 𝓢(Spacetime,ℂ)) :
    tsupport (spacetimeEventTranslationTestCLM b h : Spacetime → ℂ) ⊆
      {x : Spacetime | x-b ∈ tsupport (h : Spacetime → ℂ)} := by
  apply closure_minimal
  · intro x hx
    change h (x-b) ≠ 0 at hx
    exact subset_tsupport h hx
  · exact isClosed_closure.preimage (continuous_id.sub continuous_const)

theorem spacetimeEventTranslation_tsupport (b : Spacetime) (h : 𝓢(Spacetime,ℂ)) :
    tsupport (spacetimeEventTranslationTestCLM b h : Spacetime → ℂ)=
      eventTranslatedRegion b (tsupport (h : Spacetime → ℂ)) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨x-b,spacetimeEventTranslation_tsupport_preimage b h hx,sub_add_cancel x b⟩
  · rintro _ ⟨y,hy,rfl⟩
    have hinv : spacetimeEventTranslationTestCLM (-b) (spacetimeEventTranslationTestCLM b h)=h := by
      rw [spacetimeEventTranslationTest_add,neg_add_cancel,spacetimeEventTranslationTest_zero]
    have hy' : y ∈ tsupport
        (spacetimeEventTranslationTestCLM (-b) (spacetimeEventTranslationTestCLM b h) : Spacetime → ℂ) := by
      rw [hinv]
      exact hy
    simpa only [sub_neg_eq_add] using
      spacetimeEventTranslation_tsupport_preimage (-b) (spacetimeEventTranslationTestCLM b h) hy'

theorem spacetimeEventTranslation_compact_support (b : Spacetime) (h : 𝓢(Spacetime,ℂ))
    (hc : HasCompactSupport (h : Spacetime → ℂ)) :
    HasCompactSupport (spacetimeEventTranslationTestCLM b h : Spacetime → ℂ) := by
  change IsCompact (tsupport (spacetimeEventTranslationTestCLM b h : Spacetime → ℂ))
  rw [spacetimeEventTranslation_tsupport]
  exact hc.isCompact.image (continuous_id.add continuous_const)

theorem spacelikeSeparatedTests_eventTranslation (b : Spacetime) (h k : 𝓢(Spacetime,ℂ))
    (hs : SpacelikeSeparatedTests h k) :
    SpacelikeSeparatedTests (spacetimeEventTranslationTestCLM b h) (spacetimeEventTranslationTestCLM b k) := by
  intro x hx y hy
  rw [spacetimeEventTranslation_tsupport] at hx hy
  obtain ⟨x',hx',rfl⟩ := hx
  obtain ⟨y',hy',rfl⟩ := hy
  have he : (y'+b)-(x'+b)=y'-x' := by abel
  rw [he]
  exact hs x' hx' y' hy'

end AASCKleinGordon
