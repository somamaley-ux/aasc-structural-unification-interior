import CompletedConeClock
import Mathlib.Analysis.Convex.Topology

/-! The auxiliary compact body of SR Proposition 5.6 is derived from original
completed order. No strict physical clock or finite speed bound is input.
An auxiliary cone in R x V permits reuse of the proved compact-section lemma. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
open Set
open scoped Topology
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

def srSymmetricOrderInterval (C : Set V) (e : V) : Set V :=
  {w | e+w∈C ∧ e-w∈C}

theorem sr_original_order_interval_closed (C : Set V) (closed : IsClosed C) (e : V) :
    IsClosed (srSymmetricOrderInterval C e) :=
  (closed.preimage (continuous_const.add continuous_id)).inter
    (closed.preimage (continuous_const.sub continuous_id))

theorem sr_original_order_interval_convex (C : Set V) (convex : Convex ℝ C) (e : V) :
    Convex ℝ (srSymmetricOrderInterval C e) := by
  intro x hx y hy a b ha hb hab
  constructor
  · have hh:=convex hx.1 hy.1 ha hb hab
    have he:a • (e+x)+b • (e+y)=e+(a • x+b • y):=by
      rw [smul_add,smul_add]
      calc
        _=(a+b) • e+(a • x+b • y):=by rw [add_smul]; abel
        _=e+(a • x+b • y):=by rw [hab,one_smul]
    rwa [he] at hh
  · have hh:=convex hx.2 hy.2 ha hb hab
    have he:a • (e-x)+b • (e-y)=e-(a • x+b • y):=by
      rw [smul_sub,smul_sub]
      calc
        _=(a+b) • e-(a • x+b • y):=by rw [add_smul]; abel
        _=e-(a • x+b • y):=by rw [hab,one_smul]
    rwa [he] at hh

theorem sr_original_order_interval_zero_neighborhood (C : Set V) (e : V)
    (interiorRest : e∈interior C) : srSymmetricOrderInterval C e∈𝓝 (0:V) := by
  have hc:C∈𝓝 e:=mem_interior_iff_mem_nhds.mp interiorRest
  exact Filter.inter_mem
    ((continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hc))
    ((continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds (by simpa using hc))

theorem sr_original_pointed_order_constructs_compact_interval
    (C : Set V) (closed : IsClosed C)
    (conic : ∀ r:ℝ,0≤r → ∀ v∈C,r • v∈C)
    (pointed : ∀ v∈C,-v∈C → v=0) (e:V) :
    IsCompact (srSymmetricOrderInterval C e) := by
  let D:Set (ℝ × V):={z | 0≤z.1 ∧ z.1 • e+z.2∈C ∧ z.1 • e-z.2∈C}
  have hdclosed:IsClosed D:=
    (isClosed_le continuous_const continuous_fst).inter
      ((closed.preimage ((continuous_fst.smul continuous_const).add continuous_snd)).inter
       (closed.preimage ((continuous_fst.smul continuous_const).sub continuous_snd)))
  have hdconic:∀ r:ℝ,0≤r → ∀ z∈D,r • z∈D:=by
    intro r hr z hz
    refine ⟨mul_nonneg hr hz.1,?_,?_⟩
    · simpa only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul,mul_smul,smul_add] using conic r hr _ hz.2.1
    · simpa only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul,mul_smul,smul_sub] using conic r hr _ hz.2.2
  have hdpositive:∀ z∈D,z≠0 → 0<(ContinuousLinearMap.fst ℝ ℝ V) z:=by
    intro z hz hn
    change 0<z.1
    by_contra hh
    have ht:z.1=0:=le_antisymm (le_of_not_gt hh) hz.1
    have hp:z.2∈C:=by simpa [ht] using hz.2.1
    have hm:-z.2∈C:=by simpa [ht] using hz.2.2
    exact hn (Prod.ext ht (pointed _ hp hm))
  obtain ⟨M,_,bound⟩:=finite_comparison_bound D hdclosed hdconic
    (ContinuousLinearMap.fst ℝ ℝ V) hdpositive
  apply (isCompact_closedBall (0:V) M).of_isClosed_subset
    (sr_original_order_interval_closed C closed e)
  intro w hw
  have hh:=bound (1,w) ⟨by norm_num,by simpa using hw⟩
  have hn:‖w‖≤‖((1:ℝ),w)‖:=le_max_right _ _
  have hh':‖((1:ℝ),w)‖≤M:=by simpa using hh
  simpa only [Metric.mem_closedBall,dist_zero_right] using hn.trans hh'

theorem sr_original_rest_preserves_order_interval (C : Set V) (e:V)
    (h:V ≃L[ℝ] V) (preserves:h '' C=C) (fixes:h e=e) :
    h '' srSymmetricOrderInterval C e=srSymmetricOrderInterval C e := by
  have mem (v:V):h v∈C ↔ v∈C:=by
    calc
      h v∈C ↔ h v∈h '' C:=by rw [preserves]
      _ ↔ v∈C:=h.injective.mem_set_image
  ext w
  constructor
  · rintro ⟨v,hv,rfl⟩
    constructor
    · simpa only [map_add,fixes] using (mem (e+v)).mpr hv.1
    · simpa only [map_sub,fixes] using (mem (e-v)).mpr hv.2
  · intro hw
    refine ⟨h.symm w,?_,h.apply_symm_apply w⟩
    constructor
    · apply (mem _).mp
      simpa only [map_add,fixes,h.apply_symm_apply] using hw.1
    · apply (mem _).mp
      simpa only [map_sub,fixes,h.apply_symm_apply] using hw.2

#print axioms sr_original_order_interval_closed
#print axioms sr_original_order_interval_convex
#print axioms sr_original_order_interval_zero_neighborhood
#print axioms sr_original_pointed_order_constructs_compact_interval
#print axioms sr_original_rest_preserves_order_interval
end
end AASCMetricConstruction
