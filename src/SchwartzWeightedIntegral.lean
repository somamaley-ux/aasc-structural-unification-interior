import SchwartzPartialDerivative
import Mathlib.Analysis.Calculus.ParametricIntegral

noncomputable section
open scoped SchwartzMap ContDiff
open MeasureTheory Filter
namespace AASCKleinGordon.SchwartzOperations
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure E} {f : E → ℂ}

section Value
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedSpace ℂ V] [SMulCommClass ℝ ℂ V] [CompleteSpace V]

def weightedPartialIntegral (f : E → ℂ) (H : 𝓢(E × F,V)) (y : F) : V :=
  ∫ x, f x • H (x,y) ∂μ

theorem weighted_slice_integrable (hf : Integrable f μ) (H : 𝓢(E × F,V)) (y : F) :
    Integrable (fun x => f x • H (x,y)) μ := by
  apply (hf.norm.mul_const (SchwartzMap.seminorm ℝ 0 0 H)).mono'
    (hf.aestronglyMeasurable.smul
      (H.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
  exact ae_of_all μ fun x => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (H.norm_le_seminorm ℝ (x,y)) (norm_nonneg _)

theorem weightedPartialIntegral_hasFDerivAt (hf : Integrable f μ) (H : 𝓢(E × F,V)) (y : F) :
    HasFDerivAt (weightedPartialIntegral (μ:=μ) f H)
      (weightedPartialIntegral (μ:=μ) f (partialSndDeriv H) y) y := by
  unfold weightedPartialIntegral
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜:=ℝ) (μ:=μ)
    (F:=fun y x => f x • H (x,y)) (F':=fun y x => f x • partialSndDeriv H (x,y))
    (s:=Set.univ) (bound:=fun x =>
    ‖f x‖ * SchwartzMap.seminorm ℝ 0 0 (partialSndDeriv H)) (by simp)
  · exact Eventually.of_forall fun y => (weighted_slice_integrable hf H y).aestronglyMeasurable
  · exact weighted_slice_integrable hf H y
  · exact (weighted_slice_integrable hf (partialSndDeriv H) y).aestronglyMeasurable
  · exact ae_of_all μ fun x y _ => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left ((partialSndDeriv H).norm_le_seminorm ℝ (x,y))
        (norm_nonneg _)
  · exact hf.norm.mul_const _
  · exact ae_of_all μ fun x y _ => (hasFDerivAt_snd_slice H x y).const_smul (f x)

theorem weightedPartialIntegral_fderiv (hf : Integrable f μ) (H : 𝓢(E × F,V)) :
    fderiv ℝ (weightedPartialIntegral (μ:=μ) f H) =
      weightedPartialIntegral (μ:=μ) f (partialSndDeriv H) :=
  funext fun y => (weightedPartialIntegral_hasFDerivAt hf H y).fderiv

theorem weightedPartialIntegral_weighted_norm_le (hf : Integrable f μ)
    (H : 𝓢(E × F,V)) (k : ℕ) (y : F) :
    ‖y‖^k * ‖weightedPartialIntegral (μ:=μ) f H y‖ ≤
      (∫ x, ‖f x‖ ∂μ) * SchwartzMap.seminorm ℝ k 0 H := by
  have hw (x : E) : ‖y‖^k * ‖H (x,y)‖ ≤ SchwartzMap.seminorm ℝ k 0 H := by
    have h := H.le_seminorm ℝ k 0 (x,y)
    simp only [norm_iteratedFDeriv_zero] at h
    apply le_trans ?_ h
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_snd_le (x,y)) k
  calc
    _ = ‖(‖y‖^k : ℝ) • weightedPartialIntegral (μ:=μ) f H y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ = ‖∫ x, (‖y‖^k : ℝ) • (f x • H (x,y)) ∂μ‖ := by
      rw [weightedPartialIntegral, integral_smul]
    _ ≤ ∫ x, ‖f x‖ * SchwartzMap.seminorm ℝ k 0 H ∂μ := by
      apply norm_integral_le_of_norm_le (hf.norm.mul_const _)
      exact ae_of_all μ fun x => by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        calc
          _ = ‖f x‖ * (‖y‖^k * ‖H (x,y)‖) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hw x) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

end Value

theorem weightedPartialIntegral_contDiff_nat (hf : Integrable f μ) (n : ℕ) :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
      [SMulCommClass ℝ ℂ V] [CompleteSpace V] (H : 𝓢(E × F,V)),
      ContDiff ℝ n (weightedPartialIntegral (μ:=μ) f H) := by
  induction n with
  | zero =>
      intro V _ _ _ _ _ H
      have hd : Differentiable ℝ (weightedPartialIntegral (μ:=μ) f H) := fun y =>
        (weightedPartialIntegral_hasFDerivAt hf H y).differentiableAt
      exact contDiff_zero.mpr hd.continuous
  | succ n ih =>
      intro V _ _ _ _ _ H
      rw [show ((n+1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞)+1 by simp,
        contDiff_succ_iff_fderiv]
      refine ⟨fun y => (weightedPartialIntegral_hasFDerivAt hf H y).differentiableAt,?_,?_⟩
      · simp
      · rw [weightedPartialIntegral_fderiv hf H]
        exact ih (partialSndDeriv H)

theorem weightedPartialIntegral_smooth (hf : Integrable f μ)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
    [SMulCommClass ℝ ℂ V] [CompleteSpace V] (H : 𝓢(E × F,V)) :
    ContDiff ℝ ∞ (weightedPartialIntegral (μ:=μ) f H) :=
  contDiff_infty.mpr fun n => weightedPartialIntegral_contDiff_nat hf n H

theorem weightedPartialIntegral_derivative_bound (hf : Integrable f μ) (n : ℕ) :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
      [SMulCommClass ℝ ℂ V] [CompleteSpace V] (H : 𝓢(E × F,V)) (k : ℕ) (y : F),
      ‖y‖^k * ‖iteratedFDeriv ℝ n (weightedPartialIntegral (μ:=μ) f H) y‖ ≤
        (∫ x, ‖f x‖ ∂μ) * SchwartzMap.seminorm ℝ k n H := by
  induction n with
  | zero =>
      intro V _ _ _ _ _ H k y
      simpa only [norm_iteratedFDeriv_zero] using weightedPartialIntegral_weighted_norm_le hf H k y
  | succ n ih =>
      intro V _ _ _ _ _ H k y
      rw [← norm_iteratedFDeriv_fderiv, weightedPartialIntegral_fderiv hf H]
      exact (ih (partialSndDeriv H) k y).trans
        (mul_le_mul_of_nonneg_left (partialSndDeriv_seminorm_le H k n)
          (integral_nonneg fun x => norm_nonneg _))

section ContinuousMap
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  [SMulCommClass ℝ ℂ V] [CompleteSpace V]

def weightedPartialIntegralCLM (hf : Integrable f μ) : 𝓢(E × F,V) →L[ℂ] 𝓢(F,V) := by
  refine SchwartzMap.mkCLM (weightedPartialIntegral (μ:=μ) f)
    (fun H K y => ?_) (fun c H y => ?_) (weightedPartialIntegral_smooth hf) ?_
  · simp only [weightedPartialIntegral, SchwartzMap.add_apply, smul_add]
    exact integral_add (weighted_slice_integrable hf H y) (weighted_slice_integrable hf K y)
  · simp only [weightedPartialIntegral, SchwartzMap.smul_apply, RingHom.id_apply]
    simp_rw [smul_comm (f _) c]
    exact integral_smul c _
  · rintro ⟨k,n⟩
    refine ⟨{(k,n)}, ∫ x, ‖f x‖ ∂μ, integral_nonneg (fun x => norm_nonneg _), ?_⟩
    intro H y
    simpa only [Finset.sup_singleton] using weightedPartialIntegral_derivative_bound hf n H k y

@[simp] theorem weightedPartialIntegralCLM_apply (hf : Integrable f μ)
    (H : 𝓢(E × F,V)) (y : F) :
    weightedPartialIntegralCLM hf H y = ∫ x, f x • H (x,y) ∂μ := rfl

theorem weightedPartialIntegralCLM_seminorm_le (hf : Integrable f μ)
    (H : 𝓢(E × F,V)) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (weightedPartialIntegralCLM hf H) ≤
      (∫ x, ‖f x‖ ∂μ) * SchwartzMap.seminorm ℝ k n H := by
  apply SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity)
  exact weightedPartialIntegral_derivative_bound hf n H k

end ContinuousMap

end AASCKleinGordon.SchwartzOperations
