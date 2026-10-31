import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! Actual bounded multiplication used to construct graphs and unitary phases
of unbounded real multiplication operators. No operator/source bridge is an
input. Functions and their bounds are explicit and multiplication is defined
on actual almost-everywhere L2 classes. -/
noncomputable section
open MeasureTheory Filter
namespace AASCKleinGordon
namespace Multiplication
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
abbrev H (μ : Measure X) := Lp ℂ 2 μ

theorem bounded_mul_memLp (c : X → ℂ) (hc : AEStronglyMeasurable c μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ,‖c x‖≤C) (f : H μ) : MemLp (fun x => c x*f x) 2 μ := by
  apply (Lp.memLp f).of_le_mul (c:=C) (hc.mul (Lp.memLp f).1)
  filter_upwards [hb] with x hx
  simpa only [Pi.mul_apply,norm_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))

def boundedMulValue (c : X → ℂ) (hc : AEStronglyMeasurable c μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ,‖c x‖≤C) (f : H μ) : H μ :=
  (bounded_mul_memLp c hc C hb f).toLp (fun x => c x*f x)

theorem boundedMulValue_ae (c : X → ℂ) (hc : AEStronglyMeasurable c μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ,‖c x‖≤C) (f : H μ) :
    boundedMulValue c hc C hb f=ᵐ[μ] (fun x => c x*f x) := MemLp.coeFn_toLp _

def boundedMulLinear (c : X → ℂ) (hc : AEStronglyMeasurable c μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ,‖c x‖≤C) : H μ →ₗ[ℂ] H μ where
  toFun := boundedMulValue c hc C hb
  map_add' f g := by
    apply Lp.ext
    filter_upwards [boundedMulValue_ae c hc C hb (f+g),boundedMulValue_ae c hc C hb f,
      boundedMulValue_ae c hc C hb g,Lp.coeFn_add f g,
      Lp.coeFn_add (boundedMulValue c hc C hb f) (boundedMulValue c hc C hb g)] with x h₁ h₂ h₃ h₄ h₅
    simp only [Pi.add_apply] at h₄ h₅
    rw [h₁,h₅,h₂,h₃,h₄,mul_add]
  map_smul' z f := by
    apply Lp.ext
    filter_upwards [boundedMulValue_ae c hc C hb (z • f),boundedMulValue_ae c hc C hb f,
      Lp.coeFn_smul z f,Lp.coeFn_smul z (boundedMulValue c hc C hb f)] with x h₁ h₂ h₃ h₄
    simp only [RingHom.id_apply]
    simp only [Pi.smul_apply,smul_eq_mul] at h₃ h₄
    rw [h₁,h₄,h₂,h₃]
    change c x*(z*f x)=z*(c x*f x)
    ring

theorem boundedMulLinear_norm_le (c : X → ℂ) (hc : AEStronglyMeasurable c μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ,‖c x‖≤C) (f : H μ) :
    ‖boundedMulLinear c hc C hb f‖≤C*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedMulValue_ae c hc C hb f,hb] with x hx hbound
  change ‖boundedMulValue c hc C hb f x‖≤C*‖f x‖
  rw [hx,norm_mul]
  exact mul_le_mul_of_nonneg_right hbound (norm_nonneg _)

def boundedMul (c : X → ℂ) (hc : AEStronglyMeasurable c μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ,‖c x‖≤C) : H μ →L[ℂ] H μ :=
  (boundedMulLinear c hc C hb).mkContinuous C (boundedMulLinear_norm_le c hc C hb)

theorem boundedMul_ae (c : X → ℂ) (hc : AEStronglyMeasurable c μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ,‖c x‖≤C) (f : H μ) :
    boundedMul c hc C hb f=ᵐ[μ] (fun x => c x*f x) := boundedMulValue_ae c hc C hb f

end Multiplication
end AASCKleinGordon
