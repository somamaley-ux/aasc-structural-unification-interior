import CompletedConeClock
import Mathlib.Tactic

/-! SR 5.7: derive the full centered clock-section body from the original
completed cone and clock. Compactness, convexity and interior are proved;
the body is not a separately selected ellipsoid or metric certificate. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

abbrev SRClockSpatialSpace (τ : V →L[ℝ] ℝ):=τ.toLinearMap.ker

def srCenteredClockBody (C : Set V) (τ : V →L[ℝ] ℝ) (e : V) :
    Set (SRClockSpatialSpace τ):={x|e+(x:V)∈C}

theorem sr_spatial_clock_zero (τ : V →L[ℝ] ℝ) (x : SRClockSpatialSpace τ) :
    τ (x:V)=0 := x.property

theorem sr_clock_body_closed (C : Set V) (closed : IsClosed C)
    (τ : V →L[ℝ] ℝ) (e : V) : IsClosed (srCenteredClockBody C τ e) :=
  closed.preimage (continuous_const.add continuous_subtype_val)

theorem sr_clock_body_convex (C : Set V) (convex : Convex ℝ C)
    (τ : V →L[ℝ] ℝ) (e : V) : Convex ℝ (srCenteredClockBody C τ e) := by
  intro x hx y hy a b ha hb hab
  change e+(a • (x:V)+b • (y:V))∈C
  have he:e+(a • (x:V)+b • (y:V))=a • (e+(x:V))+b • (e+(y:V)):=by
    calc
      _=(a+b) • e+(a • (x:V)+b • (y:V)):=by rw [hab,one_smul]
      _=_:=by simp only [add_smul,smul_add];abel
  rw [he]
  exact convex hx hy ha hb hab

theorem sr_clock_body_zero_interior (C : Set V) (τ : V →L[ℝ] ℝ) (e : V)
    (interiorRest : e∈interior C) : srCenteredClockBody C τ e∈𝓝 0 := by
  have hc:Continuous (fun x:SRClockSpatialSpace τ=>e+(x:V)):=
    continuous_const.add continuous_subtype_val
  have hn:C∈𝓝 e:=mem_interior_iff_mem_nhds.mp interiorRest
  exact hc.continuousAt.preimage_mem_nhds (by simpa using hn)

theorem sr_clock_body_compact (C : Set V) (closed : IsClosed C)
    (conic : ∀ r:ℝ,0≤r → ∀ v∈C,r • v∈C)
    (τ : V →L[ℝ] ℝ) (positive : ∀ v∈C,v≠0 → 0<τ v)
    (e : V) (clockOne : τ e=1) : IsCompact (srCenteredClockBody C τ e) := by
  obtain ⟨M,_,bound⟩:=finite_comparison_bound C closed conic τ positive
  have hsubset:srCenteredClockBody C τ e⊆Metric.closedBall (0:SRClockSpatialSpace τ) (M+‖e‖):=by
    intro x hx
    have hc:τ (e+(x:V))=1:=by rw [map_add,clockOne,sr_spatial_clock_zero];ring
    have hb:=bound (e+(x:V)) hx
    rw [hc,mul_one] at hb
    have hn:‖(x:V)‖≤‖e+(x:V)‖+‖e‖:=by
      calc
        _=‖(e+(x:V))-e‖:=by congr 1;abel
        _≤_:=norm_sub_le _ _
    change dist x 0≤M+‖e‖
    rw [dist_zero_right]
    change ‖(x:V)‖≤M+‖e‖
    linarith
  exact (isCompact_closedBall (0:SRClockSpatialSpace τ) (M+‖e‖)).of_isClosed_subset
    (sr_clock_body_closed C closed τ e) hsubset

def srRestOnClockKernel (τ : V →L[ℝ] ℝ) (h : V ≃L[ℝ] V)
    (clockPreserved : ∀ v,τ (h v)=τ v) :
    SRClockSpatialSpace τ ≃L[ℝ] SRClockSpatialSpace τ :=
  (show SRClockSpatialSpace τ ≃ₗ[ℝ] SRClockSpatialSpace τ from
    { toFun:=fun x=>⟨h x,by change τ (h (x:V))=0;rw [clockPreserved];exact x.property⟩
      invFun:=fun x=>⟨h.symm x,by
        change τ (h.symm (x:V))=0
        have he:=clockPreserved (h.symm (x:V))
        rw [h.apply_symm_apply] at he
        exact he.symm.trans x.property⟩
      left_inv:=fun x=>Subtype.ext (h.symm_apply_apply x)
      right_inv:=fun x=>Subtype.ext (h.apply_symm_apply x)
      map_add':=fun x y=>Subtype.ext (map_add h (x:V) (y:V))
      map_smul':=fun r x=>Subtype.ext (map_smul h r (x:V)) }).toContinuousLinearEquiv

theorem sr_original_rest_preserves_constructed_clock_body
    (C : Set V) (τ : V →L[ℝ] ℝ) (e : V) (h : V ≃L[ℝ] V)
    (clockPreserved : ∀ v,τ (h v)=τ v) (restFixed : h e=e) (preserves : h '' C=C) :
    srRestOnClockKernel τ h clockPreserved '' srCenteredClockBody C τ e=
      srCenteredClockBody C τ e := by
  let k:=srRestOnClockKernel τ h clockPreserved
  have hi (x:SRClockSpatialSpace τ):x∈srCenteredClockBody C τ e ↔ k x∈srCenteredClockBody C τ e:=by
    have hc (v:V):h v∈C ↔ v∈C:=by
      calc
        h v∈C ↔ h v∈h '' C:=by rw [preserves]
        _ ↔ v∈C:=h.injective.mem_set_image
    have he:h (e+(x:V))=e+(h (x:V)):=by rw [map_add,restFixed]
    change e+(x:V)∈C ↔ e+h (x:V)∈C
    rw [← he]
    exact (hc _).symm
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (hi x).mp hx
  · intro hy
    refine ⟨k.symm y,?_,k.apply_symm_apply y⟩
    apply (hi (k.symm y)).mpr
    simpa only [k.apply_symm_apply] using hy

#print axioms sr_spatial_clock_zero
#print axioms sr_clock_body_closed
#print axioms sr_clock_body_convex
#print axioms sr_clock_body_zero_interior
#print axioms sr_clock_body_compact
#print axioms srRestOnClockKernel
#print axioms sr_original_rest_preserves_constructed_clock_body
end
end AASCMetricConstruction
