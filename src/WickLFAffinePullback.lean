import WickNativeAffineMetricLaws

noncomputable section
set_option maxHeartbeats 1500000
open TopologicalSpace SeminormFamily Seminorm
namespace AASCKleinGordon

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def wickLFAffineHomeomorph (b : E) (M : E ≃L[ℝ] E) : E ≃ₜ E where
  toEquiv :=
    { toFun x := b+M x
      invFun x := M.symm (x-b)
      left_inv x := by simp
      right_inv x := by simp }
  continuous_toFun := continuous_const.add M.continuous
  continuous_invFun := M.symm.continuous.comp (continuous_id.sub continuous_const)

def wickLFAffineCompact (b : E) (M : E ≃L[ℝ] E) (K : Compacts E) : Compacts E :=
  ⟨wickLFAffineHomeomorph b M '' (K : Set E),K.isCompact.image (wickLFAffineHomeomorph b M).continuous⟩

def wickSupportedAffinePullLM (b : E) (M : E ≃L[ℝ] E) (K : Compacts E) :
    ContDiffMapSupportedIn E F (⊤ : ℕ∞) K →ₗ[ℝ]
      ContDiffMapSupportedIn E F (⊤ : ℕ∞) (wickLFAffineCompact b M K) where
  toFun f := .of_support_subset
    (f.contDiff.comp (M.symm.contDiff.comp (contDiff_id.sub contDiff_const))) (by
      intro x hx
      have inside : (wickLFAffineHomeomorph b M).symm x∈Function.support f := hx
      exact ⟨(wickLFAffineHomeomorph b M).symm x,f.tsupport_subset (subset_closure inside),
        (wickLFAffineHomeomorph b M).apply_symm_apply x⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem wick_supported_affine_derivative_bound (b : E) (M : E ≃L[ℝ] E)
    (K : Compacts E) (i : ℕ) (f : ContDiffMapSupportedIn E F (⊤ : ℕ∞) K) (x : E) :
    ‖iteratedFDeriv ℝ i (wickSupportedAffinePullLM b M K f) x‖ ≤
      ‖M.symm.toContinuousLinearMap‖^i *
        ContDiffMapSupportedIn.seminorm ℝ E F (⊤ : ℕ∞) K i f := by
  change ‖iteratedFDeriv ℝ i (fun y => (f ∘ M.symm) (y-b)) x‖≤_
  rw [iteratedFDeriv_comp_sub]
  change ‖iteratedFDeriv ℝ i (f ∘ M.symm.toContinuousLinearMap) (x-b)‖≤_
  rw [M.symm.toContinuousLinearMap.iteratedFDeriv_comp_right f.contDiff (x-b) (by exact_mod_cast (le_top : (i : ℕ∞)≤⊤))]
  calc
    _ ≤ ‖iteratedFDeriv ℝ i f (M.symm (x-b))‖ *
        ∏ _ : Fin i, ‖M.symm.toContinuousLinearMap‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ContDiffMapSupportedIn.seminorm ℝ E F (⊤ : ℕ∞) K i f *
        ‖M.symm.toContinuousLinearMap‖^i := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_mul_of_nonneg_right
        (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm ℝ) (by positivity)
    _ = _ := mul_comm _ _

theorem wick_supported_affine_seminorm_bound (b : E) (M : E ≃L[ℝ] E)
    (K : Compacts E) (i : ℕ) (f : ContDiffMapSupportedIn E F (⊤ : ℕ∞) K) :
    ContDiffMapSupportedIn.seminorm ℝ E F (⊤ : ℕ∞) (wickLFAffineCompact b M K) i
      (wickSupportedAffinePullLM b M K f) ≤
        ‖M.symm.toContinuousLinearMap‖^i *
          ContDiffMapSupportedIn.seminorm ℝ E F (⊤ : ℕ∞) K i f := by
  apply (ContDiffMapSupportedIn.seminorm_le_iff ℝ
    (mul_nonneg (by positivity) (apply_nonneg _ _)) i _).mpr
  intro x _
  exact wick_supported_affine_derivative_bound b M K i f x

def wickSupportedAffinePullCLM (b : E) (M : E ≃L[ℝ] E) (K : Compacts E) :
    ContDiffMapSupportedIn E F (⊤ : ℕ∞) K →L[ℝ]
      ContDiffMapSupportedIn E F (⊤ : ℕ∞) (wickLFAffineCompact b M K) where
  toLinearMap := wickSupportedAffinePullLM b M K
  cont := by
    refine continuous_from_bounded (ContDiffMapSupportedIn.withSeminorms ℝ E F ⊤ K)
      (ContDiffMapSupportedIn.withSeminorms ℝ E F ⊤ (wickLFAffineCompact b M K)) _
      (fun i => ⟨{i},⟨‖M.symm.toContinuousLinearMap‖^i,by positivity⟩,fun f => ?_⟩)
    simpa using wick_supported_affine_seminorm_bound b M K i f

def wickAffinePullTest (b : E) (M : E ≃L[ℝ] E) {Ω Ξ : Opens E}
    (maps : Set.MapsTo (wickLFAffineHomeomorph b M) Ω Ξ)
    (f : TestFunction Ω F (⊤ : ℕ∞)) : TestFunction Ξ F (⊤ : ℕ∞) :=
  ⟨fun x => f (M.symm (x-b)),
    f.contDiff.comp (M.symm.contDiff.comp (contDiff_id.sub contDiff_const)),
    f.hasCompactSupport.comp_homeomorph (wickLFAffineHomeomorph b M).symm,by
      intro x hx
      have inside : x∈tsupport (f ∘ (wickLFAffineHomeomorph b M).symm) := hx
      rw [tsupport_comp_eq_preimage f (wickLFAffineHomeomorph b M).symm] at inside
      have out := maps (f.tsupport_subset inside)
      simpa only [Homeomorph.apply_symm_apply] using out⟩

def wickAffinePullTestCLM (b : E) (M : E ≃L[ℝ] E) {Ω Ξ : Opens E}
    (maps : Set.MapsTo (wickLFAffineHomeomorph b M) Ω Ξ) :
    TestFunction Ω F (⊤ : ℕ∞) →L[ℝ] TestFunction Ξ F (⊤ : ℕ∞) :=
  TestFunction.mkCLM ℝ (wickAffinePullTest b M maps)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun K hK => by
      have subset : (wickLFAffineCompact b M K : Set E)⊆Ξ := by
        rintro _ ⟨x,hx,rfl⟩
        exact maps (hK hx)
      exact (TestFunction.continuous_ofSupportedIn subset).comp
        (wickSupportedAffinePullCLM (F:=F) b M K).continuous)

theorem wick_affine_pull_test_apply (b : E) (M : E ≃L[ℝ] E) {Ω Ξ : Opens E}
    (maps : Set.MapsTo (wickLFAffineHomeomorph b M) Ω Ξ)
    (f : TestFunction Ω F (⊤ : ℕ∞)) (x : E) :
    wickAffinePullTestCLM b M maps f x=f (M.symm (x-b)) := rfl

end AASCKleinGordon
