import WickCovariantStrongSource
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Filter Topology
open scoped SchwartzMap
namespace AASCKleinGordon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def wickLocalizationBump (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ContDiffBump (0:E) := ⟨1,2,by norm_num,by norm_num⟩

def wickLocalizationBase (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : 𝓢(E,ℂ) :=
  ((wickLocalizationBump E).hasCompactSupport.comp_left
    (g:=Complex.ofReal) (by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (wickLocalizationBump E).contDiff)

theorem wick_localization_base_apply (x : E) :
    wickLocalizationBase E x=((wickLocalizationBump E x : ℝ) : ℂ) := rfl

theorem wick_localization_base_support : HasCompactSupport (wickLocalizationBase E) :=
  (wickLocalizationBump E).hasCompactSupport.comp_left (g:=Complex.ofReal) (by simp)

theorem wick_localization_base_one {x : E} (hx : ‖x‖≤1) :
    wickLocalizationBase E x=1 := by
  rw [wick_localization_base_apply]
  have hb := (wickLocalizationBump E).one_of_mem_closedBall
    (show x∈Metric.closedBall (0:E) (wickLocalizationBump E).rIn by simpa [wickLocalizationBump] using hx)
  rw [hb,Complex.ofReal_one]

def wickLocalizationScalarEquiv (R : ℝ) (hR : 0<R) : E ≃L[ℝ] E where
  toFun x := R⁻¹ • x
  invFun x := R • x
  left_inv x := by
    change R • (R⁻¹ • x)=x
    rw [smul_smul,mul_inv_cancel₀ hR.ne',one_smul]
  right_inv x := by
    change R⁻¹ • (R • x)=x
    rw [smul_smul,inv_mul_cancel₀ hR.ne',one_smul]
  map_add' x y := smul_add _ _ _
  map_smul' c x := smul_comm _ _ _
  continuous_toFun := continuous_id.const_smul _
  continuous_invFun := continuous_id.const_smul _

def wickLocalizationCutoff (R : ℝ) (hR : 0<R) : 𝓢(E,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (wickLocalizationScalarEquiv R hR)
    (wickLocalizationBase E)

theorem wick_localization_cutoff_apply (R : ℝ) (hR : 0<R) (x : E) :
    wickLocalizationCutoff R hR x=wickLocalizationBase E (R⁻¹ • x) := rfl

theorem wick_localization_cutoff_support (R : ℝ) (hR : 0<R) :
    HasCompactSupport (wickLocalizationCutoff (E:=E) R hR) :=
  wick_localization_base_support.comp_isClosedEmbedding
    (wickLocalizationScalarEquiv R hR).toHomeomorph.isClosedEmbedding

theorem wick_localization_cutoff_one (R : ℝ) (hR : 0<R) {x : E} (hx : ‖x‖≤R) :
    wickLocalizationCutoff R hR x=1 := by
  rw [wick_localization_cutoff_apply]
  apply wick_localization_base_one
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
  exact (inv_mul_le_one₀ hR).mpr hx

theorem wick_localization_cutoff_derivative_bound (R : ℝ) (hR : 0<R) (hR1 : 1≤R)
    (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (wickLocalizationCutoff (E:=E) R hR) x‖≤
      SchwartzMap.seminorm ℂ 0 n (wickLocalizationBase E) := by
  let L := (wickLocalizationScalarEquiv (E:=E) R hR).toContinuousLinearMap
  have hL : ‖L‖≤1 := by
    apply L.opNorm_le_bound (by norm_num)
    intro y
    change ‖R⁻¹ • y‖≤1*‖y‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
    exact mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hR1) (norm_nonneg _)
  change ‖iteratedFDeriv ℝ n ((wickLocalizationBase E) ∘ L) x‖≤_
  rw [L.iteratedFDeriv_comp_right ((wickLocalizationBase E).smooth ⊤) x (by exact_mod_cast le_top)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have hp : (∏ _i : Fin n,‖L‖)≤1 := Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hL)
  exact (mul_le_of_le_one_right (norm_nonneg _) hp).trans
    (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (wickLocalizationBase E) n (L x))

def wickSchwartzLocalize (R : ℝ) (hR : 0<R) : 𝓢(E,ℂ) →L[ℂ] 𝓢(E,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (wickLocalizationCutoff (E:=E) R hR)

theorem wick_schwartz_localize_apply (R : ℝ) (hR : 0<R) (f : 𝓢(E,ℂ)) (x : E) :
    wickSchwartzLocalize R hR f x=wickLocalizationCutoff R hR x*f x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (wickLocalizationCutoff R hR).hasTemperateGrowth f x

theorem wick_schwartz_localize_support (R : ℝ) (hR : 0<R) (f : 𝓢(E,ℂ)) :
    HasCompactSupport (wickSchwartzLocalize R hR f) := by
  apply (wick_localization_cutoff_support (E:=E) R hR).mono
  intro x hx
  simp only [Function.mem_support,wick_schwartz_localize_apply] at hx ⊢
  exact (mul_ne_zero_iff.mp hx).1

theorem wick_schwartz_localize_error_jet_zero (R : ℝ) (hR : 0<R) (f : 𝓢(E,ℂ))
    (n : ℕ) {x : E} (hx : ‖x‖<R) :
    iteratedFDeriv ℝ n (wickSchwartzLocalize R hR f-f) x=0 := by
  have he : (fun y => (wickSchwartzLocalize R hR f-f) y)=ᶠ[𝓝 x] (fun _ => (0:ℂ)) := by
    filter_upwards [((isOpen_lt continuous_norm continuous_const).mem_nhds hx)] with y hy
    simp only [SchwartzMap.sub_apply,wick_schwartz_localize_apply,
      wick_localization_cutoff_one R hR hy.le,one_mul,sub_self]
  simpa using (he.iteratedFDeriv ℝ n).self_of_nhds

end AASCKleinGordon
