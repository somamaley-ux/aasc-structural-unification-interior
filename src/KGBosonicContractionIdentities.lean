import KGBosonicInsertionFormula
import KGSchwartzContraction

noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

theorem swapDelete_zero (n : ℕ) (p : Momentum) (y : ParticleConfiguration n) :
    swapDelete n 0 (Fin.cons p y) = y := by
  funext j
  simp [swapDelete]

theorem swapDelete_cons_succ (n : ℕ) (i : Fin (n+1)) (p : Momentum)
    (y : ParticleConfiguration (n+1)) :
    swapDelete (n+1) i.succ (Fin.cons p y) =
      fun j => Fin.cons (α:=fun _ : Fin (n+1) => Momentum) p (swapDelete n i y)
        (Equiv.swap 0 i j) := by
  funext j
  cases j using Fin.cases with
  | zero =>
      cases i using Fin.cases with
      | zero => simp [swapDelete]
      | succ i =>
          have h : (1 : Fin (n+2)) ≠ i.succ.succ := by
            intro he
            have hv := congrArg Fin.val he
            simp only [Fin.val_one, Fin.val_succ] at hv
            omega
          simp [swapDelete, Equiv.swap_apply_def, h]
  | succ j =>
      by_cases h : j.succ = i
      · subst i
        simp [swapDelete]
      · simp [swapDelete, Equiv.swap_apply_def, h, Ne.symm h]

theorem bosonic_swapDelete_cons_succ (n : ℕ) (H : bosonicSchwartz (n+1))
    (i : Fin (n+1)) (p : Momentum) (y : ParticleConfiguration (n+1)) :
    H.val (swapDelete (n+1) i.succ (Fin.cons p y)) =
      H.val (Fin.cons p (swapDelete n i y)) := by
  rw [swapDelete_cons_succ]
  exact H.property (Equiv.swap 0 i) _

theorem contraction_kernel_integrable (a : Parameters) (n : ℕ) (f : 𝓢(Momentum,ℂ))
    (H : 𝓢(ParticleConfiguration (n+1),ℂ)) (y : ParticleConfiguration n) :
    Integrable (fun p => star (f p) * H (Fin.cons p y)) (wignerMeasure a) :=
  weighted_slice_integrable
    ((postcomposeCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ) f).integrable)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (joinParticleCoordinates n) H) y

theorem sqrt_particle_factor_sq (n : ℕ) :
    (Real.sqrt (n+1) : ℂ) * (Real.sqrt (n+1) : ℂ) = (n+1 : ℂ) := by
  norm_cast
  exact Real.mul_self_sqrt (by positivity)

theorem sqrt_particle_factor_cancel (n : ℕ) :
    (Real.sqrt (n+1) : ℂ) * (Real.sqrt (n+1) : ℂ) * ((n+1 : ℕ) : ℂ)⁻¹ = 1 := by
  rw [sqrt_particle_factor_sq]
  have hn : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simpa only [Nat.cast_add, Nat.cast_one] using mul_inv_cancel₀ hn

end AASCKleinGordon
