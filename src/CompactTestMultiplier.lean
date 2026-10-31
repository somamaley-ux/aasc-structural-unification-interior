import CompactTestDerivative
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Multiplication by an actual smooth coefficient is continuous on compact
smooth tests. The constants are obtained from bounded derivatives on each
compact; no global boundedness of the coefficient is required. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
open TopologicalSpace SeminormFamily Seminorm
open scoped ContDiff BigOperators NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def compactSupportedMulLM (m : E → ℝ) (hm : ContDiff ℝ (∞) m) (K : Compacts E) :
    ContDiffMapSupportedIn E ℝ (⊤ : ℕ∞) K →ₗ[ℝ]
      ContDiffMapSupportedIn E ℝ (⊤ : ℕ∞) K where
  toFun f := .of_support_subset (hm.mul f.contDiff)
    ((Function.support_mul_subset_right m f).trans (subset_trans subset_closure f.tsupport_subset))
  map_add' f g := by ext x; exact mul_add _ _ _
  map_smul' r f := by ext x; change m x * (r * f x) = r * (m x * f x); ring

theorem compact_supported_multiplier_bound (m : E → ℝ) (hm : ContDiff ℝ (∞) m)
    (K : Compacts E) (i : ℕ) :
    ∃ C : ℝ≥0, ∀ f : ContDiffMapSupportedIn E ℝ (⊤ : ℕ∞) K,
      ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K i (compactSupportedMulLM m hm K f) ≤
        C * ContDiffMapSupportedIn.supSeminorm ℝ E ℝ ⊤ K i f := by
  have bounded (j : ℕ) : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ j m x‖ ≤ C :=
    K.isCompact.exists_bound_of_continuousOn
      (hm.continuous_iteratedFDeriv (m := j)
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).continuousOn
  choose C hC using bounded
  let A : ℝ := ‖ContinuousLinearMap.mul ℝ ℝ‖ *
    ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * max (C j) 0
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨⟨A, hA⟩, fun f => ?_⟩
  rw [ContDiffMapSupportedIn.seminorm_le_iff ℝ (by positivity)]
  intro x hx
  change ‖iteratedFDeriv ℝ i (fun y => m y * f y) x‖ ≤ _
  have hb := (ContinuousLinearMap.mul ℝ ℝ).norm_iteratedFDeriv_le_of_bilinear
    hm f.contDiff x (n := i) (by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤))
  refine hb.trans ?_
  change ‖ContinuousLinearMap.mul ℝ ℝ‖ * _ ≤ A * _
  dsimp [A]
  rw [mul_assoc, Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg (ContinuousLinearMap.mul ℝ ℝ))
  apply Finset.sum_le_sum
  intro j hj
  have hc : ‖iteratedFDeriv ℝ j m x‖ ≤ max (C j) 0 := (hC j x hx).trans (le_max_left _ _)
  have hf : ‖iteratedFDeriv ℝ (i - j) f x‖ ≤
      ContDiffMapSupportedIn.supSeminorm ℝ E ℝ ⊤ K i f := by
    apply (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm ℝ).trans
    exact (Finset.le_sup (f := ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)
      (Finset.mem_Iic.mpr (Nat.sub_le i j))) f
  exact mul_le_mul (mul_le_mul_of_nonneg_left hc (by positivity)) hf (by positivity) (by positivity)

def compactSupportedMulCLM (m : E → ℝ) (hm : ContDiff ℝ (∞) m) (K : Compacts E) :
    ContDiffMapSupportedIn E ℝ (⊤ : ℕ∞) K →L[ℝ]
      ContDiffMapSupportedIn E ℝ (⊤ : ℕ∞) K where
  toLinearMap := compactSupportedMulLM m hm K
  cont := by
    refine continuous_from_bounded (ContDiffMapSupportedIn.withSeminorms' ℝ E ℝ ⊤ K)
      (ContDiffMapSupportedIn.withSeminorms ℝ E ℝ ⊤ K) _ (fun i => ?_)
    obtain ⟨C, hC⟩ := compact_supported_multiplier_bound m hm K i
    exact ⟨{i}, C, fun f => by simpa [NNReal.smul_def] using hC f⟩

def compactTestMul {Ω : Opens E} (m : E → ℝ) (hm : ContDiff ℝ (∞) m)
    (f : TestFunction Ω ℝ (⊤ : ℕ∞)) : TestFunction Ω ℝ (⊤ : ℕ∞) where
  toFun x := m x * f x
  contDiff' := hm.mul f.contDiff
  hasCompactSupport' := f.hasCompactSupport.mul_left
  tsupport_subset' := tsupport_mul_subset_right.trans f.tsupport_subset

def compactTestMulCLM (Ω : Opens E) (m : E → ℝ) (hm : ContDiff ℝ (∞) m) :
    TestFunction Ω ℝ (⊤ : ℕ∞) →L[ℝ] TestFunction Ω ℝ (⊤ : ℕ∞) :=
  TestFunction.mkCLM ℝ (compactTestMul m hm)
    (fun f g => by ext x; exact mul_add _ _ _)
    (fun r f => by ext x; change m x * (r * f x) = r * (m x * f x); ring)
    (fun K hK => (TestFunction.continuous_ofSupportedIn hK).comp
      (compactSupportedMulCLM m hm K).continuous)

theorem compact_test_multiplier_apply (Ω : Opens E) (m : E → ℝ) (hm : ContDiff ℝ (∞) m)
    (f : TestFunction Ω ℝ (⊤ : ℕ∞)) (x : E) :
    compactTestMulCLM Ω m hm f x = m x * f x := rfl

theorem compact_test_multiplier_support (Ω : Opens E) (m : E → ℝ) (hm : ContDiff ℝ (∞) m)
    (f : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    tsupport (compactTestMulCLM Ω m hm f) ⊆ tsupport f := tsupport_mul_subset_right

#print axioms compact_supported_multiplier_bound
#print axioms compact_test_multiplier_apply
#print axioms compact_test_multiplier_support
end
end AASCSemanticExhaustion
