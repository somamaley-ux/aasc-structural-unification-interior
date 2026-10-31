import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic

noncomputable section
open scoped SchwartzMap ContDiff
namespace AASCKleinGordon.SchwartzOperations
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_iteratedFDeriv_comp_contraction (L : F →L[ℝ] E) (hL : ‖L‖≤1)
    {f : E → G} (hf : ContDiff ℝ ∞ f) (x : F) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖≤‖iteratedFDeriv ℝ n f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast le_top)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hL)

theorem product_weight_bound (x : E) (y : F) (k : ℕ) :
    ‖(x,y)‖^k≤(1+‖x‖)^k*(1+‖y‖)^k := by
  rw [← mul_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [Prod.norm_def]
  apply max_le <;> nlinarith [norm_nonneg x,norm_nonneg y,mul_nonneg (norm_nonneg x) (norm_nonneg y)]

def schwartzBound {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (k n : ℕ) (f : 𝓢(D,ℂ)) : ℝ :=
  2^k*(Finset.Iic (k,n)).sup (schwartzSeminormFamily ℂ D ℂ) f

theorem schwartzBound_nonneg {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (k n : ℕ) (f : 𝓢(D,ℂ)) : 0≤schwartzBound k n f := by
  unfold schwartzBound
  positivity

theorem weighted_iteratedFDeriv_le (f : 𝓢(E,ℂ)) (k n i : ℕ) (hi : i≤n) (x : E) :
    (1+‖x‖)^k*‖iteratedFDeriv ℝ i f x‖≤schwartzBound k n f :=
  SchwartzMap.one_add_le_sup_seminorm_apply (𝕜:=ℂ) (m:=(k,n)) le_rfl hi f x

theorem tensor_derivative_term_bound (f : 𝓢(E,ℂ)) (g : 𝓢(F,ℂ))
    (k n i : ℕ) (hi : i≤n) (z : E × F) :
    ‖z‖^k*‖iteratedFDeriv ℝ i (f ∘ Prod.fst) z‖*
      ‖iteratedFDeriv ℝ (n-i) (g ∘ Prod.snd) z‖≤schwartzBound k n f*schwartzBound k n g := by
  have hf := norm_iteratedFDeriv_comp_contraction (ContinuousLinearMap.fst ℝ E F)
    (ContinuousLinearMap.norm_fst_le ℝ E F) (f.smooth ⊤) z i
  have hg := norm_iteratedFDeriv_comp_contraction (ContinuousLinearMap.snd ℝ E F)
    (ContinuousLinearMap.norm_snd_le ℝ E F) (g.smooth ⊤) z (n-i)
  have hw := product_weight_bound z.1 z.2 k
  change ‖z‖^k≤(1+‖z.1‖)^k*(1+‖z.2‖)^k at hw
  calc
    _ ≤ ((1+‖z.1‖)^k*(1+‖z.2‖)^k)*‖iteratedFDeriv ℝ i f z.1‖*
        ‖iteratedFDeriv ℝ (n-i) g z.2‖ := by
      apply mul_le_mul _ hg (norm_nonneg _) (by positivity)
      exact mul_le_mul hw hf (norm_nonneg _) (by positivity)
    _ = ((1+‖z.1‖)^k*‖iteratedFDeriv ℝ i f z.1‖)*
        ((1+‖z.2‖)^k*‖iteratedFDeriv ℝ (n-i) g z.2‖) := by ring
    _ ≤ schwartzBound k n f*schwartzBound k n g :=
      mul_le_mul (weighted_iteratedFDeriv_le f k n i hi z.1)
        (weighted_iteratedFDeriv_le g k n (n-i) (Nat.sub_le _ _) z.2)
        (by positivity) (schwartzBound_nonneg k n f)

def realComplexMultiplication : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ

theorem tensor_iteratedFDeriv_bound (f : 𝓢(E,ℂ)) (g : 𝓢(F,ℂ)) (k n : ℕ) (z : E × F) :
    ‖z‖^k*‖iteratedFDeriv ℝ n (fun z : E × F => f z.1*g z.2) z‖≤
      ‖realComplexMultiplication‖*(∑ i ∈ Finset.range (n+1),(n.choose i : ℝ))*
        schwartzBound k n f*schwartzBound k n g := by
  have hb := realComplexMultiplication.norm_iteratedFDeriv_le_of_bilinear
    ((f.smooth ⊤).comp (ContinuousLinearMap.fst ℝ E F).contDiff)
    ((g.smooth ⊤).comp (ContinuousLinearMap.snd ℝ E F).contDiff) z
    (n:=n) (by exact_mod_cast le_top)
  change ‖iteratedFDeriv ℝ n (fun z : E × F => f z.1*g z.2) z‖≤_ at hb
  calc
    _ ≤ ‖z‖^k*(‖realComplexMultiplication‖*∑ i ∈ Finset.range (n+1),
        (n.choose i : ℝ)*‖iteratedFDeriv ℝ i (f ∘ Prod.fst) z‖*
          ‖iteratedFDeriv ℝ (n-i) (g ∘ Prod.snd) z‖) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ‖realComplexMultiplication‖*∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*
        (‖z‖^k*‖iteratedFDeriv ℝ i (f ∘ Prod.fst) z‖*
          ‖iteratedFDeriv ℝ (n-i) (g ∘ Prod.snd) z‖) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ‖realComplexMultiplication‖*∑ i ∈ Finset.range (n+1),
        (n.choose i : ℝ)*(schwartzBound k n f*schwartzBound k n g) := by
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg realComplexMultiplication)
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (tensor_derivative_term_bound f g k n i (Finset.mem_range_succ_iff.mp hi) z)
        (by positivity)
    _ = _ := by rw [← Finset.sum_mul]; ring

end AASCKleinGordon.SchwartzOperations
