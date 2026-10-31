import L2RealMultiplicationCoefficients

noncomputable section
open MeasureTheory Filter
namespace AASCKleinGordon
namespace Multiplication
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem realMultiplicationGraph_eq_kernel (v : X → ℝ) (hv : Measurable v) :
    realMultiplicationGraph (μ:=μ) v=
      ((graphBoundedB v hv).comp (ContinuousLinearMap.snd ℂ (H μ) (H μ))-
        (graphBoundedA v hv).comp (ContinuousLinearMap.fst ℂ (H μ) (H μ))).ker := by
  ext z
  constructor
  · intro hz
    change graphBoundedB v hv z.2-graphBoundedA v hv z.1=0
    apply sub_eq_zero.mpr
    apply Lp.ext
    filter_upwards [graphBoundedB_ae v hv z.2,graphBoundedA_ae v hv z.1,hz] with x hb ha hx
    rw [hb,ha,hx,graphCoefficientA]
    ring
  · intro hz
    change graphBoundedB v hv z.2-graphBoundedA v hv z.1=0 at hz
    have he := sub_eq_zero.mp hz
    filter_upwards [graphBoundedB_ae v hv z.2,graphBoundedA_ae v hv z.1] with x hb ha
    change z.2 x=(v x : ℂ)*z.1 x
    have hx := congrArg (fun f : H μ => f x) he
    change (graphBoundedB v hv z.2) x=(graphBoundedA v hv z.1) x at hx
    rw [hb,ha] at hx
    apply mul_left_cancel₀ (graphCoefficientB_ne_zero (v x))
    calc
      graphCoefficientB (v x)*z.2 x=graphCoefficientA (v x)*z.1 x := hx
      _ = graphCoefficientB (v x)*((v x : ℂ)*z.1 x) := by rw [graphCoefficientA]; ring

theorem realMultiplication_isClosed (v : X → ℝ) (hv : Measurable v) :
    (realMultiplication v : H μ →ₗ.[ℂ] H μ).IsClosed := by
  change IsClosed ((realMultiplication (μ:=μ) v).graph : Set (H μ × H μ))
  rw [realMultiplication_graph,realMultiplicationGraph_eq_kernel v hv]
  exact ContinuousLinearMap.isClosed_ker _

theorem realMultiplication_formally_symmetric (v : X → ℝ) :
    (realMultiplication v : H μ →ₗ.[ℂ] H μ).IsFormalAdjoint (realMultiplication v) := by
  intro f g
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [realMultiplication_apply_ae v f,realMultiplication_apply_ae v g] with x hf hg
  rw [hf,hg]
  simp [RCLike.inner_apply,map_mul]
  ring

theorem realMultiplication_graph_on_B (v : X → ℝ) (hv : Measurable v) (f : H μ) :
    (graphBoundedB v hv f,graphBoundedA v hv f) ∈ (realMultiplication v).graph := by
  apply (realMultiplication_mem_graph v _ _).2
  filter_upwards [graphBoundedB_ae v hv f,graphBoundedA_ae v hv f] with x hb ha
  rw [hb,ha,graphCoefficientA]
  ring

theorem realMultiplication_B_mem_domain (v : X → ℝ) (hv : Measurable v) (f : H μ) :
    graphBoundedB v hv f ∈ (realMultiplication v).domain :=
  LinearPMap.mem_domain_of_mem_graph (realMultiplication_graph_on_B v hv f)

theorem realMultiplication_on_B (v : X → ℝ) (hv : Measurable v) (f : H μ) :
    realMultiplication v ⟨graphBoundedB v hv f,realMultiplication_B_mem_domain v hv f⟩=
      graphBoundedA v hv f :=
  LinearPMap.mem_graph_snd_inj (realMultiplication v)
    ((realMultiplication v).mem_graph ⟨_,realMultiplication_B_mem_domain v hv f⟩)
    (realMultiplication_graph_on_B v hv f) rfl

theorem graphBoundedB_dense (v : X → ℝ) (hv : Measurable v) : DenseRange (graphBoundedB (μ:=μ) v hv) :=
  boundedMul_real_nonzero_dense _ _ 1 (Eventually.of_forall (fun x => graphCoefficientB_bound (v x)))
    (Eventually.of_forall (fun x => graphCoefficientB_real (v x)))
    (Eventually.of_forall (fun x => graphCoefficientB_ne_zero (v x)))

theorem realMultiplication_dense_domain (v : X → ℝ) (hv : Measurable v) :
    Dense ((realMultiplication (μ:=μ) v).domain : Set (H μ)) := by
  apply (graphBoundedB_dense v hv).mono
  rintro f ⟨g,rfl⟩
  exact realMultiplication_B_mem_domain v hv g

end Multiplication
end AASCKleinGordon
