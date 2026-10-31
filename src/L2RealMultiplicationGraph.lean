import L2BoundedMultiplication

noncomputable section
open MeasureTheory Filter
namespace AASCKleinGordon
namespace Multiplication
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def realMultiplicationGraph (v : X → ℝ) : Submodule ℂ (H μ × H μ) where
  carrier := {z | z.2=ᵐ[μ] (fun x => (v x : ℂ)*z.1 x)}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    change (0 : H μ) x=0 at hx
    change (0 : H μ) x=(v x : ℂ)*(0 : H μ) x
    rw [hx, mul_zero]
  add_mem' := by
    intro f g hf hg
    filter_upwards [hf,hg,Lp.coeFn_add f.1 g.1,Lp.coeFn_add f.2 g.2] with x h₁ h₂ h₃ h₄
    change (f.2+g.2) x=(v x : ℂ)*(f.1+g.1) x
    simp only [Pi.add_apply] at h₃ h₄
    rw [h₃,h₄,h₁,h₂,mul_add]
  smul_mem' := by
    intro c f hf
    filter_upwards [hf,Lp.coeFn_smul c f.1,Lp.coeFn_smul c f.2] with x h₁ h₂ h₃
    change (c • f.2) x=(v x : ℂ)*(c • f.1) x
    simp only [Pi.smul_apply,smul_eq_mul] at h₂ h₃
    rw [h₂,h₃,h₁]
    ring

theorem realMultiplicationGraph_vertical_unique (v : X → ℝ) :
    ∀ z : H μ × H μ,z ∈ realMultiplicationGraph v → z.1=0 → z.2=0 := by
  intro z hz h0
  apply Lp.ext
  filter_upwards [hz,Lp.coeFn_zero ℂ 2 μ] with x hx hzero
  change (0 : H μ) x=0 at hzero
  change z.2 x=(0 : H μ) x
  change z.2 x=(v x : ℂ)*z.1 x at hx
  rw [h0,hzero,mul_zero] at hx
  rw [hx,hzero]

def realMultiplication (v : X → ℝ) : H μ →ₗ.[ℂ] H μ :=
  (realMultiplicationGraph v).toLinearPMap

theorem realMultiplication_graph (v : X → ℝ) :
    (realMultiplication v : H μ →ₗ.[ℂ] H μ).graph=realMultiplicationGraph v :=
  Submodule.toLinearPMap_graph_eq _ (realMultiplicationGraph_vertical_unique v)

theorem realMultiplication_mem_graph (v : X → ℝ) (f g : H μ) :
    (f,g) ∈ (realMultiplication v).graph ↔ g=ᵐ[μ] (fun x => (v x : ℂ)*f x) := by
  rw [realMultiplication_graph]
  rfl

theorem realMultiplication_apply_ae (v : X → ℝ) (f : (realMultiplication v : H μ →ₗ.[ℂ] H μ).domain) :
    realMultiplication v f=ᵐ[μ] (fun x => (v x : ℂ)*f.val x) :=
  (realMultiplication_mem_graph v _ _).1 ((realMultiplication v).mem_graph f)

theorem realMultiplication_exact_domain (v : X → ℝ) (f : H μ) :
    f ∈ (realMultiplication v).domain ↔ MemLp (fun x => (v x : ℂ)*f x) 2 μ := by
  constructor
  · intro hf
    exact (Lp.memLp (realMultiplication v ⟨f,hf⟩)).ae_eq (realMultiplication_apply_ae v ⟨f,hf⟩)
  · intro hf
    exact LinearPMap.mem_domain_of_mem_graph ((realMultiplication_mem_graph v f (hf.toLp _)).2 hf.coeFn_toLp)

end Multiplication
end AASCKleinGordon
