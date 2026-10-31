import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.LinearPMap

noncomputable section
namespace AASCKleinGordon.UnitaryCore
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedSpace ℝ H]

omit [NormedSpace ℝ H] in
theorem scaled_skew_pair_symmetric (s : ℂ) (hs : star s = -s) (x y dx dy : H)
    (h : inner ℂ dx y+inner ℂ x dy=0) : inner ℂ (s • dx) y=inner ℂ x (s • dy) := by
  rw [inner_smul_left,inner_smul_right]
  change star s*inner ℂ dx y=s*inner ℂ x dy
  rw [hs]
  linear_combination -s*h

theorem orbit_tangents_skew (U : ℝ → H ≃ₗᵢ[ℂ] H) (hzero : ∀ x,U 0 x=x)
    (x y dx dy : H) (hx : HasDerivAt (fun r => U r x) dx 0)
    (hy : HasDerivAt (fun r => U r y) dy 0) :
    inner ℂ dx y+inner ℂ x dy=0 := by
  have h := hx.inner ℂ hy
  have hc : HasDerivAt (fun r : ℝ => inner ℂ (U r x) (U r y)) 0 0 := by
    simpa only [LinearIsometryEquiv.inner_map_map] using hasDerivAt_const (0 : ℝ) (inner ℂ x y)
  simpa only [hzero,add_comm] using h.unique hc

theorem generator_commutes_of_invariant_core
    (κ : ℂ) (hκ : κ≠0) (U : ℝ → H ≃ₗᵢ[ℂ] H)
    (hg : ∀ r s x,U r (U s x)=U (r+s) x)
    (T : H →ₗ.[ℂ] H) (hp : ∀ r (x : T.domain),U r x.val∈T.domain)
    (hf : ∀ x : T.domain,HasDerivAt (fun r => U r x.val) (κ • T x) 0)
    (r : ℝ) (x : T.domain) : T ⟨U r x.val,hp r x⟩=U r (T x) := by
  have hl := hf ⟨U r x.val,hp r x⟩
  have hr : HasDerivAt (fun t : ℝ => U r (U t x.val)) (U r (κ • T x)) 0 :=
    ((U r).toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hf x)
  have he : (fun t : ℝ => U t (U r x.val))=(fun t : ℝ => U r (U t x.val)) := by
    funext t
    rw [hg,hg,add_comm]
  rw [he] at hl
  have h := congrArg (fun z : H => κ⁻¹ • z) (hl.unique hr)
  simpa only [map_smul,smul_smul,inv_mul_cancel₀ hκ,one_smul] using h

end AASCKleinGordon.UnitaryCore
