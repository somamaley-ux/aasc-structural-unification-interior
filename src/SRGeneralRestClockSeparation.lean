import SRPointedOrderInterval
import SRAuxiliaryInvariantForm
import SRCompactConvexHull
import Mathlib.Analysis.Convex.Gauge

/-! SR Proposition 5.6 for an arbitrary actual rest group. Compactness of its
orbit, the invariant auxiliary form and the fixed minimizer are constructed.
There is no finite-group, compact-group, strict-clock or finite-bound premise. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open Set
open scoped Topology BigOperators Pointwise
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V]

theorem sr_positive_quadratic_minimizer_unique (Q:QuadraticForm ℝ V) (positive:Q.PosDef)
    (S:Set V) (convex:Convex ℝ S) (x y:V) (hx:x∈S) (hy:y∈S)
    (minx:IsMinOn Q S x) (miny:IsMinOn Q S y) : x=y := by
  by_contra hn
  have hp:=positive (x-y) (sub_ne_zero.mpr hn)
  have hid:Q (x+y)+Q (x-y)=2*Q x+2*Q y:=by
    simp only [← QuadraticMap.associated_eq_self_apply ℝ Q,map_add,map_sub,
      LinearMap.add_apply,LinearMap.sub_apply]
    ring
  have hm:(1/2:ℝ) • (x+y)∈S:=by
    rw [smul_add]
    exact convex hx hy (by norm_num) (by norm_num) (by norm_num)
  have h1:=minx hm
  have h2:=miny hm
  change Q x≤Q ((1/2:ℝ) • (x+y)) at h1
  change Q y≤Q ((1/2:ℝ) • (x+y)) at h2
  rw [Q.map_smul] at h1 h2
  change Q x≤((1/2:ℝ)*(1/2))*Q (x+y) at h1
  change Q y≤((1/2:ℝ)*(1/2))*Q (x+y) at h2
  nlinarith

private theorem sr_sum_mem_cone {ι:Type*} [DecidableEq ι] (C:Set V)
    (zeroMem:(0:V)∈C) (addMem:∀ u∈C,∀ v∈C,u+v∈C)
    (s:Finset ι) (z:ι→V) (hz:∀ i∈s,z i∈C) : ∑ i∈s,z i∈C := by
  induction s using Finset.induction_on with
  | empty=>simpa using zeroMem
  | @insert i s hn ih=>
    rw [Finset.sum_insert hn]
    exact addMem _ (hz _ (Finset.mem_insert_self i s)) _
      (ih (fun j hj=>hz j (Finset.mem_insert_of_mem hj)))

theorem sr_pointed_cone_excludes_zero_convex_hull_of_nonzero_records
    (C:Set V) (zeroMem:(0:V)∈C) (addMem:∀ u∈C,∀ v∈C,u+v∈C)
    (conic:∀ r:ℝ,0≤r → ∀ v∈C,r • v∈C)
    (pointed:∀ v∈C,-v∈C → v=0) (L:Set V) (subset:L⊆C)
    (nonzero:∀ v∈L,v≠0) : (0:V)∉convexHull ℝ L := by
  classical
  intro hz
  obtain ⟨ι,fi,z,w,hz,_,hw,hs,he⟩:=eq_pos_convex_span_of_mem_convexHull hz
  have hi:Nonempty ι:=by
    by_contra hn
    haveI:IsEmpty ι:=not_nonempty_iff.mp hn
    simp at hs
  letI:=hi
  let j:ι:=Classical.arbitrary ι
  have hzj:z j∈L:=hz ⟨j,rfl⟩
  let u:V:=∑ i∈Finset.univ.erase j,w i • z i
  have hu:u∈C:=sr_sum_mem_cone C zeroMem addMem _ _
    (fun i _=>conic _ (hw i).le _ (subset (hz ⟨i,rfl⟩)))
  have huadd:u+w j • z j=0:=by
    simpa only [u] using (Finset.sum_erase_add Finset.univ
      (fun i=>w i • z i) (Finset.mem_univ j)).trans he
  have hneg:-z j∈C:=by
    have hh:=conic (w j)⁻¹ (inv_pos.mpr (hw j)).le u hu
    have hu':u=-(w j • z j):=eq_neg_of_add_eq_zero_left huadd
    simpa only [hu',smul_neg,inv_smul_smul₀ (ne_of_gt (hw j))] using hh
  exact nonzero _ hzj (pointed _ (subset hzj) hneg)

theorem sr_positive_clock_of_general_original_rest_action
    (C:Set V) (closed:IsClosed C) (convex:Convex ℝ C)
    (zeroMem:(0:V)∈C) (addMem:∀ u∈C,∀ v∈C,u+v∈C)
    (conic:∀ r:ℝ,0≤r → ∀ v∈C,r • v∈C)
    (pointed:∀ v∈C,-v∈C → v=0) (e:V) (interiorRest:e∈interior C)
    (τ:V →L[ℝ] ℝ) (weak:∀ v∈C,0≤τ v)
    {H:Type*} [Group H] (ρ:H →* (V ≃L[ℝ] V))
    (preserves:∀ h,ρ h '' C=C) (clockPreserved:∀ h v,τ (ρ h v)=τ v)
    (restFixed:∀ h,ρ h e=e)
    (noFixedSpatial:∀ v,τ v=0 → (∀ h,ρ h v=v) → v=0) :
    ∀ x∈C,x≠0 → 0<τ x := by
  classical
  let O:=srSymmetricOrderInterval C e
  have hoc:IsCompact O:=sr_original_pointed_order_constructs_compact_interval C closed conic pointed e
  have hon:O∈𝓝 (0:V):=sr_original_order_interval_zero_neighborhood C e interiorRest
  have hop (h:H):ρ h '' O=O:=sr_original_rest_preserves_order_interval C e (ρ h) (preserves h) (restFixed h)
  obtain ⟨Q,hq,hqc,hqi⟩:=sr_compact_original_body_constructs_invariant_auxiliary_form O hoc hon (fun h=>ρ h) hop
  intro x hx hn
  by_contra hnot
  have ht:τ x=0:=le_antisymm (le_of_not_gt hnot) (weak x hx)
  let orbit:Set V:=Set.range (fun h:H=>ρ h x)
  let L:Set V:=closure orbit
  have hxorb:x∈orbit:=⟨1,by change ρ 1 x=x;rw [map_one];rfl⟩
  obtain ⟨r,hr,hrx⟩:=(absorbent_nhds_zero hon).gauge_set_nonempty (x:=x)
  have horbound:orbit⊆r • O:=by
    rintro _ ⟨h,rfl⟩
    obtain ⟨w,hw,he⟩:=hrx
    refine ⟨ρ h w,?_,?_⟩
    · have hm:ρ h w∈ρ h '' O:=⟨w,hw,rfl⟩
      rwa [hop h] at hm
    · simpa only [map_smul] using congrArg (ρ h) he
  have hlcompact:IsCompact L:=(hoc.smul r).of_isClosed_subset isClosed_closure
    (closure_minimal horbound (hoc.smul r).isClosed)
  have hlcone:L⊆C:=closure_minimal (by
    rintro _ ⟨h,rfl⟩
    have hm:ρ h x∈ρ h '' C:=⟨x,hx,rfl⟩
    rwa [preserves h] at hm) closed
  have hlclock:∀ v∈L,τ v=0:=by
    apply closure_minimal _ (isClosed_eq τ.continuous continuous_const)
    rintro _ ⟨h,rfl⟩
    change τ (ρ h x)=0
    rw [clockPreserved,ht]
  have hlquad:∀ v∈L,Q v=Q x:=by
    apply closure_minimal _ (isClosed_eq hqc continuous_const)
    rintro _ ⟨h,rfl⟩
    exact hqi h x
  have hlnonzero:∀ v∈L,v≠0:=by
    intro v hv he
    have hh:=hlquad v hv
    rw [he,map_zero] at hh
    exact (ne_of_gt (hq x hn)) hh.symm
  have horpres (h:H):ρ h '' orbit=orbit:=by
    ext v
    constructor
    · rintro ⟨_,⟨k,rfl⟩,rfl⟩
      exact ⟨h*k,by change ρ (h*k) x=ρ h (ρ k x);rw [map_mul];rfl⟩
    · rintro ⟨k,rfl⟩
      refine ⟨ρ (h⁻¹*k) x,⟨h⁻¹*k,rfl⟩,?_⟩
      change (ρ h * ρ (h⁻¹*k)) x=ρ k x
      rw [← map_mul,mul_inv_cancel_left]
  have hlpres (h:H):ρ h '' L=L:=by
    change (ρ h).toHomeomorph '' closure orbit=closure orbit
    rw [(ρ h).toHomeomorph.image_closure]
    exact congrArg closure (horpres h)
  let S:Set V:=convexHull ℝ L
  have hscompact:IsCompact S:=sr_compact_set_has_compact_convex_hull L hlcompact
  have hsnonempty:S.Nonempty:=⟨x,subset_convexHull ℝ L (subset_closure hxorb)⟩
  have hspres (h:H):ρ h '' S=S:=by
    change (ρ h).toLinearMap '' convexHull ℝ L=convexHull ℝ L
    rw [(ρ h).toLinearMap.image_convexHull]
    exact congrArg (convexHull ℝ) (hlpres h)
  have hsclock:∀ v∈S,τ v=0:=convexHull_min hlclock
    (τ.toLinearMap.ker.convex)
  obtain ⟨y,hy,hmin⟩:=hscompact.exists_isMinOn hsnonempty hqc.continuousOn
  have hyfixed:∀ h,ρ h y=y:=by
    intro h
    have hhy:ρ h y∈S:=by
      have hm:ρ h y∈ρ h '' S:=⟨y,hy,rfl⟩
      rwa [hspres h] at hm
    have hhmin:IsMinOn Q S (ρ h y):=by
      intro v hv
      change Q (ρ h y)≤Q v
      rw [hqi]
      exact hmin hv
    exact sr_positive_quadratic_minimizer_unique Q hq S (convex_convexHull ℝ L)
      (ρ h y) y hhy hy hhmin hmin
  have hyzero:y=0:=noFixedSpatial y (hsclock y hy) hyfixed
  have hnzero:=sr_pointed_cone_excludes_zero_convex_hull_of_nonzero_records
    C zeroMem addMem conic pointed L hlcone hlnonzero
  exact hnzero (hyzero ▸ hy)

#print axioms sr_positive_quadratic_minimizer_unique
#print axioms sr_pointed_cone_excludes_zero_convex_hull_of_nonzero_records
#print axioms sr_positive_clock_of_general_original_rest_action
end
end AASCMetricConstruction
