import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Filter Topology
open scoped SchwartzMap
namespace AASCKleinGordon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual translation on the original Schwartz space. -/
def wickSchwartzTranslate (a : E) : 𝓢(E,ℂ) →L[ℂ] 𝓢(E,ℂ) :=
  SchwartzMap.compCLM ℂ
    (Function.HasTemperateGrowth.id'.sub (Function.HasTemperateGrowth.const a))
    ⟨1,‖a‖+1,fun x => by
      simp only [pow_one,Pi.sub_apply]
      have ht := norm_add_le (x-a) a
      rw [sub_add_cancel] at ht
      nlinarith [mul_nonneg (norm_nonneg a) (norm_nonneg (x-a))]⟩

theorem wick_schwartz_translate_apply (a : E) (f : 𝓢(E,ℂ)) (x : E) :
    wickSchwartzTranslate a f x=f (x-a) := rfl

theorem wick_schwartz_translate_zero (f : 𝓢(E,ℂ)) : wickSchwartzTranslate (0:E) f=f := by
  ext x
  simp only [wick_schwartz_translate_apply,sub_zero]

theorem wick_schwartz_translate_compact (a : E) (f : 𝓢(E,ℂ))
    (hf : HasCompactSupport f) : HasCompactSupport (wickSchwartzTranslate a f) :=
  hf.comp_homeomorph (Homeomorph.subRight a)

theorem wick_schwartz_translate_jet (a : E) (f : 𝓢(E,ℂ)) (n : ℕ) (x : E) :
    iteratedFDeriv ℝ n (wickSchwartzTranslate a f) x=iteratedFDeriv ℝ n f (x-a) :=
  iteratedFDeriv_comp_sub n a x

/-- A uniform derivative translation estimate, with an actual next-jet bound. -/
theorem wick_schwartz_derivative_translate_bound (f : 𝓢(E,ℂ)) (n : ℕ) (a b x : E) :
    ‖iteratedFDeriv ℝ n f (x-a)-iteratedFDeriv ℝ n f (x-b)‖ ≤
      SchwartzMap.seminorm ℂ 0 (n+1) f*‖a-b‖ := by
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (𝕜:=ℝ) (f:=iteratedFDeriv ℝ n f) (s:=Set.univ)
    (fun y _ => (f.smooth ⊤).differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top n) y)
    (fun y _ => by
      rw [norm_fderiv_iteratedFDeriv]
      exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f (n+1) y)
    convex_univ (Set.mem_univ (x-b)) (Set.mem_univ (x-a))
  simpa only [sub_sub_sub_cancel_left,norm_sub_rev a b] using h

/-- Compact support yields one common radius for every derivative jet. -/
theorem wick_compact_schwartz_jet_radius (f : 𝓢(E,ℂ)) (hf : HasCompactSupport f) :
    ∃ R : ℝ,0<R ∧ ∀ n x,R<‖x‖ → iteratedFDeriv ℝ n f x=0 := by
  obtain ⟨R,hR,hsub⟩ := hf.isBounded.subset_closedBall_lt 0 (0:E)
  refine ⟨R,hR,?_⟩
  intro n x hx
  by_contra hn
  have hm := hsub (support_iteratedFDeriv_subset n (show x∈Function.support (iteratedFDeriv ℝ n f) from hn))
  exact (not_le.mpr hx) (by simpa only [Metric.mem_closedBall,dist_zero_right] using hm)

/-- Every finite weighted derivative has an actual local Lipschitz translation bound.
The support hypothesis is on the original test, not a desired density conclusion. -/
theorem wick_compact_translate_seminorm_bound (f : 𝓢(E,ℂ))
    {R T : ℝ} (hR : 0<R) (hT : 0≤T)
    (hradius : ∀ n x,R<‖x‖ → iteratedFDeriv ℝ n f x=0)
    (k n : ℕ) {a b : E} (ha : ‖a‖≤T) (hb : ‖b‖≤T) :
    SchwartzMap.seminorm ℂ k n (wickSchwartzTranslate a f-wickSchwartzTranslate b f) ≤
      ((R+T)^k*SchwartzMap.seminorm ℂ 0 (n+1) f)*‖a-b‖ := by
  apply SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity)
  intro x
  have he : iteratedFDeriv ℝ n (wickSchwartzTranslate a f-wickSchwartzTranslate b f) x=
      iteratedFDeriv ℝ n f (x-a)-iteratedFDeriv ℝ n f (x-b) := by
    rw [show (⇑(wickSchwartzTranslate a f-wickSchwartzTranslate b f) : E → ℂ)=
      (fun x => wickSchwartzTranslate a f x-wickSchwartzTranslate b f x) from rfl]
    change iteratedFDeriv ℝ n ((⇑(wickSchwartzTranslate a f) : E → ℂ)+
      -(⇑(wickSchwartzTranslate b f) : E → ℂ)) x=_
    have hn : ContDiffAt ℝ n (-(⇑(wickSchwartzTranslate b f) : E → ℂ)) x :=
      (((wickSchwartzTranslate b f).smooth n).neg).contDiffAt
    have hadd := iteratedFDeriv_add_apply (𝕜:=ℝ) (i:=n)
      (f:=(⇑(wickSchwartzTranslate a f) : E → ℂ))
      (g:=-(⇑(wickSchwartzTranslate b f) : E → ℂ))
      ((wickSchwartzTranslate a f).smooth n).contDiffAt hn
    rw [hadd]
    rw [iteratedFDeriv_neg_apply,wick_schwartz_translate_jet,wick_schwartz_translate_jet]
    rfl
  rw [he]
  by_cases hx : ‖x‖≤R+T
  · calc
      _ ≤ (R+T)^k*(SchwartzMap.seminorm ℂ 0 (n+1) f*‖a-b‖) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx k)
          (wick_schwartz_derivative_translate_bound f n a b x) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have hxa : R<‖x-a‖ := by
      have ht := norm_add_le (x-a) a
      rw [sub_add_cancel] at ht
      linarith
    have hxb : R<‖x-b‖ := by
      have ht := norm_add_le (x-b) b
      rw [sub_add_cancel] at ht
      linarith
    rw [hradius n (x-a) hxa,hradius n (x-b) hxb,sub_self,norm_zero,mul_zero]
    positivity

end AASCKleinGordon
