import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.FunProp

/-! Finite-dimensional compact convex-hull infrastructure for the original
rest-orbit proof. The finite bound follows from Caratheodory, not a hypothesis
that a desired orbit hull is compact. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open Set
open scoped BigOperators
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem sr_compact_set_has_compact_convex_hull (L:Set V) (compact:IsCompact L) :
    IsCompact (convexHull ℝ L) := by
  classical
  let N:=Module.finrank ℝ V+1
  let F (m:ℕ):Set V:=
    (fun p:(Fin m → ℝ) × (Fin m → V)=>∑ i,p.1 i • p.2 i) ''
      ((stdSimplex ℝ (Fin m)) ×ˢ Set.pi Set.univ (fun _=>L))
  have hc (m:ℕ):IsCompact (F m):=by
    apply ((isCompact_stdSimplex (Fin m)).prod (isCompact_univ_pi (fun _=>compact))).image
    fun_prop
  have he:convexHull ℝ L=⋃ m:Fin (N+1),F m.val:=by
    ext x
    constructor
    · intro hx
      obtain ⟨ι,fi,z,w,hz,hi,hw,hs,hx⟩:=eq_pos_convex_span_of_mem_convexHull hx
      let m:ℕ:=Fintype.card ι
      have hm:m≤N:=(hi.card_le_finrank_succ).trans
        (Nat.add_le_add_right (Submodule.finrank_le _) 1)
      let f:ι ≃ Fin m:=Fintype.equivFin ι
      have hsum:∑ j:Fin m,w (f.symm j)=1:=by
        rw [← hs]
        exact Fintype.sum_equiv f.symm _ _ (fun _=>rfl)
      apply Set.mem_iUnion.mpr
      refine ⟨⟨m,Nat.lt_succ_of_le hm⟩,?_,?_⟩
      · exact (fun j=>w (f.symm j),fun j=>z (f.symm j))
      · refine ⟨⟨⟨fun j=>(hw _).le,hsum⟩,fun j _=>hz ⟨f.symm j,rfl⟩⟩,?_⟩
        change (∑ j:Fin m,w (f.symm j) • z (f.symm j))=x
        rw [← hx]
        exact Fintype.sum_equiv f.symm _ _ (fun _=>rfl)
    · intro hx
      obtain ⟨m,⟨⟨w,z⟩,⟨hw,hz⟩,rfl⟩⟩:=Set.mem_iUnion.mp hx
      change (∑ i,w i • z i)∈convexHull ℝ L
      change (∀ i,0≤w i) ∧ (∑ i,w i)=1 at hw
      rw [← Finset.univ.centerMass_eq_of_sum_1 z hw.2]
      apply (convex_convexHull ℝ L).centerMass_mem
      · exact fun i _=>hw.1 i
      · simpa only [hw.2] using (zero_lt_one: (0:ℝ)<1)
      · exact fun i _=>subset_convexHull ℝ L (hz i (Set.mem_univ i))
  rw [he]
  exact isCompact_iUnion (fun m=>hc m.val)

#print axioms sr_compact_set_has_compact_convex_hull
end
end AASCMetricConstruction
