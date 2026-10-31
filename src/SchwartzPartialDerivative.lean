import SchwartzPostcomposition
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic

noncomputable section
open scoped SchwartzMap ContDiff
namespace AASCKleinGordon.SchwartzOperations
variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def sndRestrictionCLM : ((E × F) →L[ℝ] V) →L[ℝ] (F →L[ℝ] V) :=
  (ContinuousLinearMap.compL ℝ F (E × F) V).flip (ContinuousLinearMap.inr ℝ E F)

@[simp] theorem sndRestrictionCLM_apply (L : (E × F) →L[ℝ] V) :
    sndRestrictionCLM L = L.comp (ContinuousLinearMap.inr ℝ E F) := rfl

theorem norm_sndRestrictionCLM_le : ‖sndRestrictionCLM (E:=E) (F:=F) (V:=V)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro L
  change ‖L.comp (ContinuousLinearMap.inr ℝ E F)‖ ≤ 1 * ‖L‖
  rw [one_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one ℝ E F))

def partialSndDeriv : 𝓢(E × F,V) →L[ℝ] 𝓢(E × F,F →L[ℝ] V) :=
  (postcomposeCLM sndRestrictionCLM).comp (SchwartzMap.fderivCLM ℝ (E × F) V)

@[simp] theorem partialSndDeriv_apply (H : 𝓢(E × F,V)) (z : E × F) :
    partialSndDeriv H z = (fderiv ℝ H z).comp (ContinuousLinearMap.inr ℝ E F) := rfl

theorem norm_iteratedFDeriv_partialSndDeriv_le (H : 𝓢(E × F,V)) (n : ℕ) (z : E × F) :
    ‖iteratedFDeriv ℝ n (partialSndDeriv H) z‖ ≤ ‖iteratedFDeriv ℝ (n+1) H z‖ := by
  have h := (sndRestrictionCLM (E:=E) (F:=F) (V:=V)).norm_iteratedFDeriv_comp_left
    ((SchwartzMap.fderivCLM ℝ (E × F) V H).contDiffAt ⊤ (x:=z)) (n:=n) (by exact_mod_cast le_top)
  change ‖iteratedFDeriv ℝ n (partialSndDeriv H) z‖ ≤ _ at h
  apply h.trans
  apply (mul_le_of_le_one_left (norm_nonneg _) norm_sndRestrictionCLM_le).trans
  exact le_of_eq (norm_iteratedFDeriv_fderiv (f:= (H : E × F → V)))

theorem partialSndDeriv_seminorm_le (H : 𝓢(E × F,V)) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (partialSndDeriv H) ≤ SchwartzMap.seminorm ℝ k (n+1) H := by
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (apply_nonneg _ _)
  intro z
  exact (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_partialSndDeriv_le H n z)
    (by positivity)).trans (H.le_seminorm ℝ k (n+1) z)

theorem hasFDerivAt_snd_slice (H : 𝓢(E × F,V)) (x : E) (y : F) :
    HasFDerivAt (fun y => H (x,y)) (partialSndDeriv H (x,y)) y := by
  convert (H.differentiableAt (x:=(x,y))).hasFDerivAt.comp y
    ((hasFDerivAt_const x y).prodMk (hasFDerivAt_id y)) using 1 <;> rfl

end AASCKleinGordon.SchwartzOperations
