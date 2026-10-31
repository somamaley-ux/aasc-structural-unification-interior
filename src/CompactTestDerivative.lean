import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Tactic

/-! Actual continuous differentiation on the smooth compact-test LF space.
Continuity is proved by the derivative seminorm shift on each fixed compact;
no derivative-continuity certificate is received. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
open TopologicalSpace SeminormFamily Seminorm
open scoped ContDiff Distributions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def compactSupportedFDerivLM (K : Compacts E) :
    ContDiffMapSupportedIn E F (⊤ : ℕ∞) K →ₗ[ℝ]
      ContDiffMapSupportedIn E (E →L[ℝ] F) (⊤ : ℕ∞) K where
  toFun f := .of_support_subset (f.contDiff.fderiv_right (by simp))
    ((support_fderiv_subset ℝ).trans f.tsupport_subset)
  map_add' f g := by
    apply ContDiffMapSupportedIn.ext
    intro x
    exact fderiv_add (f.contDiff.differentiable (by simp) x)
      (g.contDiff.differentiable (by simp) x)
  map_smul' r f := by
    apply ContDiffMapSupportedIn.ext
    intro x
    exact fderiv_const_smul (f.contDiff.differentiable (by simp) x) r

theorem compact_supported_fderiv_seminorm_bound (K : Compacts E) (i : ℕ)
    (f : ContDiffMapSupportedIn E F (⊤ : ℕ∞) K) :
    ContDiffMapSupportedIn.seminorm ℝ E (E →L[ℝ] F) (⊤ : ℕ∞) K i
        (compactSupportedFDerivLM K f) ≤
      ContDiffMapSupportedIn.seminorm ℝ E F (⊤ : ℕ∞) K (i + 1) f := by
  rw [ContDiffMapSupportedIn.seminorm_le_iff ℝ (apply_nonneg _ _)]
  intro x _
  change ‖iteratedFDeriv ℝ i (fderiv ℝ f) x‖ ≤ _
  rw [norm_iteratedFDeriv_fderiv]
  exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm ℝ

def compactSupportedFDerivCLM (K : Compacts E) :
    ContDiffMapSupportedIn E F (⊤ : ℕ∞) K →L[ℝ]
      ContDiffMapSupportedIn E (E →L[ℝ] F) (⊤ : ℕ∞) K where
  toLinearMap := compactSupportedFDerivLM K
  cont := by
    refine continuous_from_bounded (ContDiffMapSupportedIn.withSeminorms ℝ E F ⊤ K)
      (ContDiffMapSupportedIn.withSeminorms ℝ E (E →L[ℝ] F) ⊤ K) _
      (fun i => ⟨{i + 1}, 1, fun f => ?_⟩)
    simpa using compact_supported_fderiv_seminorm_bound K i f

def compactTestFDeriv {Ω : Opens E} (f : TestFunction Ω F (⊤ : ℕ∞)) :
    TestFunction Ω (E →L[ℝ] F) (⊤ : ℕ∞) where
  toFun := fderiv ℝ f
  contDiff' := f.contDiff.fderiv_right (by simp)
  hasCompactSupport' := f.hasCompactSupport.fderiv ℝ
  tsupport_subset' := (tsupport_fderiv_subset ℝ).trans f.tsupport_subset

def compactTestFDerivCLM (Ω : Opens E) :
    TestFunction Ω F (⊤ : ℕ∞) →L[ℝ] TestFunction Ω (E →L[ℝ] F) (⊤ : ℕ∞) :=
  TestFunction.mkCLM ℝ compactTestFDeriv
    (fun f g => by
      apply TestFunction.ext
      intro x
      exact fderiv_add (f.contDiff.differentiable (by simp) x)
        (g.contDiff.differentiable (by simp) x))
    (fun r f => by
      apply TestFunction.ext
      intro x
      exact fderiv_const_smul (f.contDiff.differentiable (by simp) x) r)
    (fun K hK => by
      exact (TestFunction.continuous_ofSupportedIn hK).comp
        (compactSupportedFDerivCLM (F := F) K).continuous)

theorem compact_test_fderiv_apply (Ω : Opens E)
    (f : TestFunction Ω F (⊤ : ℕ∞)) (x : E) :
    compactTestFDerivCLM Ω f x = fderiv ℝ f x := rfl

theorem compact_test_fderiv_support (Ω : Opens E)
    (f : TestFunction Ω F (⊤ : ℕ∞)) :
    tsupport (compactTestFDerivCLM Ω f) ⊆ tsupport f :=
  tsupport_fderiv_subset ℝ

#print axioms compact_supported_fderiv_seminorm_bound
#print axioms compact_test_fderiv_apply
#print axioms compact_test_fderiv_support
end
end AASCSemanticExhaustion
