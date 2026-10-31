import KGCoreFieldOperations
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory
open scoped SchwartzMap DirectSum
namespace AASCKleinGordon

theorem cons_cons_swap (n : ℕ) (p q : Momentum) (y : ParticleConfiguration n) :
    Fin.cons p (Fin.cons q y) = fun i =>
      Fin.cons (α:=fun _ : Fin (n+2) => Momentum) q (Fin.cons p y) (Equiv.swap 0 1 i) := by
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
      cases i using Fin.cases with
      | zero =>
          change q = Fin.cons (α:=fun _ : Fin (n+2) => Momentum) q (Fin.cons p y) (Equiv.swap 0 1 1)
          simp
      | succ i =>
          have hi0 : i.succ.succ ≠ (0 : Fin (n+2)) := by simp
          have hi1 : i.succ.succ ≠ (1 : Fin (n+2)) := by
            intro he
            have hv := congrArg Fin.val he
            simp only [Fin.val_succ, Fin.val_one] at hv
            omega
          simp [Equiv.swap_apply_of_ne_of_ne hi0 hi1]

theorem bosonic_cons_cons_swap (n : ℕ) (H : bosonicSchwartz (n+2))
    (p q : Momentum) (y : ParticleConfiguration n) :
    H.val (Fin.cons p (Fin.cons q y)) = H.val (Fin.cons q (Fin.cons p y)) := by
  rw [cons_cons_swap]
  exact H.property (Equiv.swap 0 1) _

theorem double_contraction_integrable (a : Parameters) (n : ℕ) (f g : 𝓢(Momentum,ℂ))
    (H : 𝓢(ParticleConfiguration (n+2),ℂ)) (y : ParticleConfiguration n) :
    Integrable (fun z : Momentum × Momentum =>
      (star (f z.1) * star (g z.2)) * H (Fin.cons z.2 (Fin.cons z.1 y)))
      ((wignerMeasure a).prod (wignerMeasure a)) := by
  have hC : Continuous (fun z : Momentum × Momentum =>
      (Fin.cons z.2 (Fin.cons z.1 y) : ParticleConfiguration (n+2))) := by
    apply continuous_pi
    intro i
    cases i using Fin.cases with
    | zero => exact continuous_snd
    | succ i =>
        cases i using Fin.cases with
        | zero => exact continuous_fst
        | succ i => exact continuous_const
  have hm : Continuous (fun z : Momentum × Momentum =>
      (star (f z.1) * star (g z.2)) * H (Fin.cons z.2 (Fin.cons z.1 y))) :=
    ((f.continuous.comp continuous_fst).star.mul
      (g.continuous.comp continuous_snd).star).mul (H.continuous.comp hC)
  apply (((f.integrable (μ:=wignerMeasure a)).norm.mul_prod
    (g.integrable (μ:=wignerMeasure a)).norm).mul_const (SchwartzMap.seminorm ℝ 0 0 H)).mono'
    hm.aestronglyMeasurable
  exact ae_of_all _ fun z => by
    simp only [norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_left (H.norm_le_seminorm ℝ _) (by positivity)

theorem annihilation_annihilation_sector_apply (a : Parameters) (n : ℕ)
    (f g : 𝓢(Momentum,ℂ)) (H : bosonicSchwartz (n+2)) (y : ParticleConfiguration n) :
    (annihilationSectorCLM a n f (annihilationSectorCLM a (n+1) g H)).val y =
      ((Real.sqrt (n+1) : ℂ) * (Real.sqrt (n+1+1) : ℂ)) *
        ∫ p, ∫ q, (star (f p) * star (g q)) * H.val (Fin.cons q (Fin.cons p y))
          ∂wignerMeasure a ∂wignerMeasure a := by
  rw [annihilationSectorCLM_apply]
  simp_rw [annihilationSectorCLM_apply]
  simp only [Nat.cast_add, Nat.cast_one]
  have he (p : Momentum) :
      star (f p) * ((Real.sqrt (n+1+1) : ℂ) *
        ∫ q, star (g q) * H.val (Fin.cons q (Fin.cons p y)) ∂wignerMeasure a) =
      (Real.sqrt (n+1+1) : ℂ) * ∫ q, (star (f p) * star (g q)) *
        H.val (Fin.cons q (Fin.cons p y)) ∂wignerMeasure a := by
    rw [show star (f p) * ((Real.sqrt (n+1+1) : ℂ) *
        ∫ q, star (g q) * H.val (Fin.cons q (Fin.cons p y)) ∂wignerMeasure a) =
      (Real.sqrt (n+1+1) : ℂ) * (star (f p) *
        ∫ q, star (g q) * H.val (Fin.cons q (Fin.cons p y)) ∂wignerMeasure a) by ring]
    rw [← integral_const_mul]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun q => by ring
  simp_rw [he]
  rw [integral_const_mul]
  ring

theorem annihilationSectors_commute (a : Parameters) (n : ℕ) (f g : 𝓢(Momentum,ℂ))
    (H : bosonicSchwartz (n+2)) :
    annihilationSectorCLM a n f (annihilationSectorCLM a (n+1) g H) =
      annihilationSectorCLM a n g (annihilationSectorCLM a (n+1) f H) := by
  apply Subtype.ext
  ext y
  rw [annihilation_annihilation_sector_apply, annihilation_annihilation_sector_apply]
  congr 1
  rw [integral_integral_swap (double_contraction_integrable a n f g H.val y)]
  apply integral_congr_ae
  exact ae_of_all _ fun q => by
    apply integral_congr_ae
    exact ae_of_all _ fun p => by
      change (star (f p) * star (g q)) * H.val (Fin.cons q (Fin.cons p y)) =
        (star (g q) * star (f p)) * H.val (Fin.cons p (Fin.cons q y))
      rw [bosonic_cons_cons_swap]
      ring

theorem annihilationCore_commute (a : Parameters) (f g : 𝓢(Momentum,ℂ)) :
    (annihilationCore a f).comp (annihilationCore a g) =
      (annihilationCore a g).comp (annihilationCore a f) := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro H
  cases n with
  | zero => simp [LinearMap.comp_apply]
  | succ n =>
      cases n with
      | zero => simp [LinearMap.comp_apply]
      | succ n =>
          simp only [LinearMap.comp_apply, annihilationCore_lof_succ]
          rw [annihilationSectors_commute]

end AASCKleinGordon
