import L2RealMultiplicationClosed

noncomputable section
open MeasureTheory
namespace AASCKleinGordon
namespace Multiplication
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem realMultiplication_selfAdjoint (v : X → ℝ) (hv : Measurable v) :
    IsSelfAdjoint (realMultiplication v : H μ →ₗ.[ℂ] H μ) := by
  let T : H μ →ₗ.[ℂ] H μ := realMultiplication v
  have hd := realMultiplication_dense_domain (μ:=μ) v hv
  have lower : T ≤ T.adjoint := (realMultiplication_formally_symmetric v).le_adjoint hd
  have upper : T.adjoint ≤ T := by
    apply LinearPMap.le_of_le_graph
    intro z hz
    obtain ⟨y,rfl⟩ := (LinearPMap.mem_graph_iff' _).mp hz
    have heq : graphBoundedB v hv (T.adjoint y)=graphBoundedA v hv y.val := by
      apply ext_inner_right ℂ
      intro h
      calc
        inner ℂ (graphBoundedB v hv (T.adjoint y)) h=
            inner ℂ (T.adjoint y) (graphBoundedB v hv h) :=
          boundedMul_symmetric _ _ _ _ (Filter.Eventually.of_forall (fun x => graphCoefficientB_real (v x))) _ _
        _ = inner ℂ y.val (T ⟨graphBoundedB v hv h,realMultiplication_B_mem_domain v hv h⟩) :=
          LinearPMap.adjoint_isFormalAdjoint hd y ⟨_,realMultiplication_B_mem_domain v hv h⟩
        _ = inner ℂ y.val (graphBoundedA v hv h) := by rw [realMultiplication_on_B]
        _ = inner ℂ (graphBoundedA v hv y.val) h :=
          (boundedMul_symmetric _ _ _ _ (Filter.Eventually.of_forall (fun x => graphCoefficientA_real (v x))) _ _).symm
    change (y.val,T.adjoint y) ∈ (realMultiplication v).graph
    rw [realMultiplication_graph,realMultiplicationGraph_eq_kernel v hv]
    change graphBoundedB v hv (T.adjoint y)-graphBoundedA v hv y.val=0
    exact sub_eq_zero.mpr heq
  exact LinearPMap.isSelfAdjoint_def.mpr (le_antisymm upper lower)

end Multiplication
end AASCKleinGordon
