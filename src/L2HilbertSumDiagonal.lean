import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section
namespace AASCKleinGordon.HilbertSum
variable {ι : Type*} {E : ι → Type*}
  [∀ i,NormedAddCommGroup (E i)] [∀ i,InnerProductSpace ℂ (E i)]

theorem diagonal_mem (C : ∀ i,E i →L[ℂ] E i)
    (hb : ∀ i f,‖C i f‖≤‖f‖) (f : lp E 2) : Memℓp (fun i => C i (f i)) 2 := by
  apply memℓp_gen
  apply Summable.of_nonneg_of_le (fun i => Real.rpow_nonneg (norm_nonneg _) _)
    (fun i => Real.rpow_le_rpow (norm_nonneg _) (hb i (f i)) (by norm_num))
    ((lp.memℓp f).summable (by norm_num))

def diagonalLinear (C : ∀ i,E i →L[ℂ] E i)
    (hb : ∀ i f,‖C i f‖≤‖f‖) : lp E 2 →ₗ[ℂ] lp E 2 where
  toFun f := ⟨fun i => C i (f i),diagonal_mem C hb f⟩
  map_add' f g := lp.ext (funext (fun i => (C i).map_add (f i) (g i)))
  map_smul' c f := lp.ext (funext (fun i => (C i).map_smul c (f i)))

theorem diagonalLinear_norm_le (C : ∀ i,E i →L[ℂ] E i)
    (hb : ∀ i f,‖C i f‖≤‖f‖) (f : lp E 2) : ‖diagonalLinear C hb f‖≤‖f‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg _)
  intro s
  calc
    ∑ i ∈ s,‖diagonalLinear C hb f i‖^(2 : ENNReal).toReal ≤
        ∑ i ∈ s,‖f i‖^(2 : ENNReal).toReal := by
      apply Finset.sum_le_sum
      intro i hi
      exact Real.rpow_le_rpow (norm_nonneg _) (hb i (f i)) (by norm_num)
    _ ≤ ‖f‖^(2 : ENNReal).toReal := lp.sum_rpow_le_norm_rpow (by norm_num) f s

def diagonal (C : ∀ i,E i →L[ℂ] E i)
    (hb : ∀ i f,‖C i f‖≤‖f‖) : lp E 2 →L[ℂ] lp E 2 :=
  (diagonalLinear C hb).mkContinuous 1 (fun f => by simpa using diagonalLinear_norm_le C hb f)

@[simp] theorem diagonal_apply (C : ∀ i,E i →L[ℂ] E i)
    (hb : ∀ i f,‖C i f‖≤‖f‖) (f : lp E 2) (i : ι) :
    diagonal C hb f i=C i (f i) := rfl

theorem diagonal_symmetric (C : ∀ i,E i →L[ℂ] E i)
    (hb : ∀ i f,‖C i f‖≤‖f‖)
    (hs : ∀ i f g,inner ℂ (C i f) g=inner ℂ f (C i g)) (f g : lp E 2) :
    inner ℂ (diagonal C hb f) g=inner ℂ f (diagonal C hb g) := by
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  exact hs i (f i) (g i)

theorem diagonal_injective (C : ∀ i,E i →L[ℂ] E i)
    (hb : ∀ i f,‖C i f‖≤‖f‖) (hi : ∀ i,Function.Injective (C i)) :
    Function.Injective (diagonal C hb) := by
  intro f g h
  apply lp.ext
  funext i
  exact hi i (congrArg (fun u : lp E 2 => u i) h)

end AASCKleinGordon.HilbertSum
