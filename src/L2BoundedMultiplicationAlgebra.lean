import L2BoundedMultiplication
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

noncomputable section
open MeasureTheory Filter
namespace AASCKleinGordon
namespace Multiplication
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem boundedMul_symmetric (c : X → ℂ) (hc : AEStronglyMeasurable c μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ,‖c x‖≤C) (hr : ∀ᵐ x ∂μ,star (c x)=c x)
    (f g : H μ) : inner ℂ (boundedMul c hc C hb f) g=inner ℂ f (boundedMul c hc C hb g) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedMul_ae c hc C hb f,boundedMul_ae c hc C hb g,hr] with x hx hy hz
  rw [hx,hy]
  simp only [RCLike.inner_apply,map_mul]
  have hz' : (starRingEnd ℂ) (c x)=c x := hz
  rw [hz']
  ring

theorem boundedMul_injective (c : X → ℂ) (hc : AEStronglyMeasurable c μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ,‖c x‖≤C) (hn : ∀ᵐ x ∂μ,c x≠0) :
    Function.Injective (boundedMul c hc C hb) := by
  intro f g h
  apply Lp.ext
  filter_upwards [boundedMul_ae c hc C hb f,boundedMul_ae c hc C hb g,hn] with x hx hy hz
  apply mul_left_cancel₀ hz
  rw [← hx,← hy]
  exact congrArg (fun v : H μ => v x) h

theorem symmetric_injective_has_dense_range (B : H μ →L[ℂ] H μ)
    (symm : ∀ f g,inner ℂ (B f) g=inner ℂ f (B g)) (inj : Function.Injective B) : DenseRange B := by
  have ho : (LinearMap.range B.toLinearMap)ᗮ=⊥ := by
    apply le_antisymm ?_ bot_le
    intro y hy
    change y=0
    apply inj
    rw [map_zero]
    apply (inner_self_eq_zero (𝕜:=ℂ)).mp
    have h := (Submodule.mem_orthogonal _ y).mp hy (B (B y)) ⟨B y,rfl⟩
    simpa only [symm] using h
  have hd := (Submodule.topologicalClosure_eq_top_iff (K:=LinearMap.range B.toLinearMap)).2 ho
  intro y
  change y ∈ (LinearMap.range B.toLinearMap).topologicalClosure
  rw [hd]
  trivial

theorem boundedMul_real_nonzero_dense (c : X → ℂ) (hc : AEStronglyMeasurable c μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ,‖c x‖≤C) (hr : ∀ᵐ x ∂μ,star (c x)=c x)
    (hn : ∀ᵐ x ∂μ,c x≠0) : DenseRange (boundedMul c hc C hb) :=
  symmetric_injective_has_dense_range _ (boundedMul_symmetric c hc C hb hr)
    (boundedMul_injective c hc C hb hn)

end Multiplication
end AASCKleinGordon
