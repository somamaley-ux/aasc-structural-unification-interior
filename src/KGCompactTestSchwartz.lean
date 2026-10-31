import KGOriginalWickActionReality
import CompactTestDerivative

/-! Actual fixed-compact seminorm estimates and LF inclusion into Schwartz
space. No target continuity is assumed. -/
noncomputable section
set_option maxHeartbeats 8000000
open TopologicalSpace SeminormFamily Seminorm
open scoped SchwartzMap ContDiff
namespace AASCKleinGordon

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def wickSupportedToSchwartzLM (K : Compacts E) :
    ContDiffMapSupportedIn E F (⊤ : ℕ∞) K →ₗ[ℝ] 𝓢(E,F) where
  toFun f := f.hasCompactSupport.toSchwartzMap f.contDiff
  map_add' f g := by ext x; rfl
  map_smul' r f := by ext x; rfl

theorem wick_supported_schwartz_seminorm_bound (K : Compacts E) (R : ℝ)
    (hR : 0 ≤ R) (bound : ∀ x∈K,‖x‖≤R) (k n : ℕ)
    (f : ContDiffMapSupportedIn E F (⊤ : ℕ∞) K) :
    SchwartzMap.seminorm ℝ k n (wickSupportedToSchwartzLM K f) ≤
      R^k * ContDiffMapSupportedIn.seminorm ℝ E F (⊤ : ℕ∞) K n f := by
  apply SchwartzMap.seminorm_le_bound
  · positivity
  · intro x
    change ‖x‖^k * ‖iteratedFDeriv ℝ n f x‖ ≤ _
    by_cases hx : x∈K
    · exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (bound x hx) k)
        (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm ℝ)
        (norm_nonneg _) (pow_nonneg hR k)
    · rw [f.iteratedFDeriv_zero_on_compl hx]
      simp only [Pi.zero_apply,norm_zero,mul_zero]
      positivity

def wickSupportedToSchwartzCLM (K : Compacts E) :
    ContDiffMapSupportedIn E F (⊤ : ℕ∞) K →L[ℝ] 𝓢(E,F) where
  toLinearMap := wickSupportedToSchwartzLM K
  cont := by
    obtain ⟨R,hR⟩ := K.isCompact.exists_bound_of_continuousOn (f:=fun x:E=>x) continuous_id.continuousOn
    refine continuous_from_bounded (ContDiffMapSupportedIn.withSeminorms ℝ E F ⊤ K)
      (schwartz_withSeminorms ℝ E F) _ (fun i => ⟨{i.2},⟨(max R 0)^i.1,by positivity⟩,fun f => ?_⟩)
    simpa using wick_supported_schwartz_seminorm_bound K (max R 0) (le_max_right _ _)
      (fun x hx => (hR x hx).trans (le_max_left _ _)) i.1 i.2 f

def wickCompactTestToSchwartz (Ω : Opens E) (f : TestFunction Ω F (⊤ : ℕ∞)) : 𝓢(E,F) :=
  f.hasCompactSupport.toSchwartzMap f.contDiff

def wickCompactTestToSchwartzCLM (Ω : Opens E) :
    TestFunction Ω F (⊤ : ℕ∞) →L[ℝ] 𝓢(E,F) :=
  TestFunction.mkCLM ℝ (wickCompactTestToSchwartz Ω)
    (fun f g => by ext x; rfl) (fun r f => by ext x; rfl)
    (fun K hK => (wickSupportedToSchwartzCLM (F:=F) K).continuous)

theorem wick_compact_test_to_schwartz_apply (Ω : Opens E)
    (f : TestFunction Ω F (⊤ : ℕ∞)) (x : E) :
    wickCompactTestToSchwartzCLM Ω f x=f x := rfl

theorem wick_compact_test_to_schwartz_LF_continuous (Ω : Opens E) :
    Continuous (wickCompactTestToSchwartzCLM (F:=F) Ω) :=
  (wickCompactTestToSchwartzCLM Ω).continuous

end AASCKleinGordon
