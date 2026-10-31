import L2BoundedMultiplication
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section
namespace AASCKleinGordon.Translation

def phase (hbar t r : ℝ) : ℂ := Complex.exp (((-t*r/hbar : ℝ) : ℂ)*Complex.I)

@[simp] theorem phase_zero (hbar r : ℝ) : phase hbar 0 r=1 := by simp [phase]

theorem phase_add (hbar t s r : ℝ) : phase hbar (t+s) r=phase hbar t r*phase hbar s r := by
  rw [phase,phase,phase,← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] theorem phase_norm (hbar t r : ℝ) : ‖phase hbar t r‖=1 := by
  simp [phase,Complex.norm_exp]

theorem phase_inverse (hbar t r : ℝ) : phase hbar (-t) r*phase hbar t r=1 := by
  rw [← phase_add,neg_add_cancel,phase_zero]

end AASCKleinGordon.Translation

open MeasureTheory Filter
namespace AASCKleinGordon.Multiplication
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem translationPhase_measurable (v : X → ℝ) (hv : Measurable v) (hbar t : ℝ) :
    Measurable (fun x => Translation.phase hbar t (v x)) := by
  unfold Translation.phase
  fun_prop

def phaseMultiplier (v : X → ℝ) (hv : Measurable v) (hbar t : ℝ) : H μ →L[ℂ] H μ :=
  boundedMul (fun x => Translation.phase hbar t (v x))
    (translationPhase_measurable v hv hbar t).aestronglyMeasurable 1
    (Eventually.of_forall (fun x => (Translation.phase_norm hbar t (v x)).le))

theorem phaseMultiplier_ae (v : X → ℝ) (hv : Measurable v) (hbar t : ℝ) (f : H μ) :
    phaseMultiplier v hv hbar t f=ᵐ[μ] (fun x => Translation.phase hbar t (v x)*f x) :=
  boundedMul_ae _ _ _ _ f

theorem phaseMultiplier_zero (v : X → ℝ) (hv : Measurable v) (hbar : ℝ) (f : H μ) :
    phaseMultiplier v hv hbar 0 f=f := by
  apply Lp.ext
  filter_upwards [phaseMultiplier_ae v hv hbar 0 f] with x hx
  simpa only [Translation.phase_zero,one_mul] using hx

theorem phaseMultiplier_add (v : X → ℝ) (hv : Measurable v) (hbar t s : ℝ) (f : H μ) :
    phaseMultiplier v hv hbar (t+s) f=phaseMultiplier v hv hbar t (phaseMultiplier v hv hbar s f) := by
  apply Lp.ext
  filter_upwards [phaseMultiplier_ae v hv hbar (t+s) f,
    phaseMultiplier_ae v hv hbar t (phaseMultiplier v hv hbar s f),
    phaseMultiplier_ae v hv hbar s f] with x h1 h2 h3
  rw [h1,h2,h3,Translation.phase_add,mul_assoc]

theorem phaseMultiplier_contraction (v : X → ℝ) (hv : Measurable v) (hbar t : ℝ) (f : H μ) :
    ‖phaseMultiplier v hv hbar t f‖≤‖f‖ := by
  simpa only [one_mul] using boundedMulLinear_norm_le _
    (translationPhase_measurable v hv hbar t).aestronglyMeasurable 1
    (Eventually.of_forall (fun x => (Translation.phase_norm hbar t (v x)).le)) f

theorem phaseMultiplier_inverse (v : X → ℝ) (hv : Measurable v) (hbar t : ℝ) (f : H μ) :
    phaseMultiplier v hv hbar (-t) (phaseMultiplier v hv hbar t f)=f := by
  rw [← phaseMultiplier_add,neg_add_cancel,phaseMultiplier_zero]

theorem phaseMultiplier_norm (v : X → ℝ) (hv : Measurable v) (hbar t : ℝ) (f : H μ) :
    ‖phaseMultiplier v hv hbar t f‖=‖f‖ := by
  apply le_antisymm (phaseMultiplier_contraction v hv hbar t f)
  have h := phaseMultiplier_contraction v hv hbar (-t) (phaseMultiplier v hv hbar t f)
  rwa [phaseMultiplier_inverse] at h

def phaseUnitary (v : X → ℝ) (hv : Measurable v) (hbar t : ℝ) : H μ ≃ₗᵢ[ℂ] H μ where
  toFun := phaseMultiplier v hv hbar t
  invFun := phaseMultiplier v hv hbar (-t)
  left_inv := phaseMultiplier_inverse v hv hbar t
  right_inv f := by
    have h := phaseMultiplier_inverse v hv hbar (-t) f
    simpa only [neg_neg] using h
  map_add' := (phaseMultiplier v hv hbar t).map_add
  map_smul' := (phaseMultiplier v hv hbar t).map_smul
  norm_map' := phaseMultiplier_norm v hv hbar t

end AASCKleinGordon.Multiplication
