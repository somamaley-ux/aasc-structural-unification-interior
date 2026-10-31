import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! The radial part of SR 5.7, on the full bounded convex neighbourhood.
This intermediate lemma will be applied to the constructed covariance inverse;
it does not assert that supplying a positive form constructs that covariance. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sr_gauge_normalization_on_full_boundary (K : Set E) (convex : Convex ℝ K)
    (zeroInterior : K∈𝓝 (0:E)) (bounded : Bornology.IsBounded K)
    (x : E) (hx : x≠0) :
    (gauge K x)⁻¹ • x∈frontier K := by
  have hg:0<gauge K x:=(gauge_pos (absorbent_nhds_zero zeroInterior)
    (NormedSpace.isVonNBounded_of_isBounded ℝ bounded)).mpr hx
  apply (gauge_eq_one_iff_mem_frontier convex zeroInterior).mp
  rw [gauge_smul_of_nonneg (inv_nonneg.mpr hg.le),smul_eq_mul,
    inv_mul_cancel₀ hg.ne']

theorem sr_full_isotropy_fixes_quadratic_boundary_radius [Nontrivial E]
    (K : Set E) (convex : Convex ℝ K) (zeroInterior : K∈𝓝 (0:E))
    (bounded : Bornology.IsBounded K) {H : Type*} (rest : H → E ≃L[ℝ] E)
    (isotropy : ∀ x∈frontier K,∀ y∈frontier K,∃ h,rest h x=y)
    (Q : QuadraticForm ℝ E) (positive : Q.PosDef)
    (invariant : ∀ h x,Q (rest h x)=Q x) :
    ∃ c:ℝ,0<c ∧ ∀ x,Q x=c*(gauge K x)^2 := by
  obtain ⟨e,he⟩:=exists_ne (0:E)
  let u:E:=(gauge K e)⁻¹ • e
  have hu:u∈frontier K:=sr_gauge_normalization_on_full_boundary K convex zeroInterior bounded e he
  have hge:0<gauge K e:=(gauge_pos (absorbent_nhds_zero zeroInterior)
    (NormedSpace.isVonNBounded_of_isBounded ℝ bounded)).mpr he
  have hune:u≠0:=smul_ne_zero (inv_ne_zero hge.ne') he
  refine ⟨Q u,positive u hune,?_⟩
  intro x
  by_cases hx:x=0
  · simp [hx]
  · have hg:0<gauge K x:=(gauge_pos (absorbent_nhds_zero zeroInterior)
      (NormedSpace.isVonNBounded_of_isBounded ℝ bounded)).mpr hx
    let v:E:=(gauge K x)⁻¹ • x
    have hv:v∈frontier K:=sr_gauge_normalization_on_full_boundary K convex zeroInterior bounded x hx
    obtain ⟨h,hh⟩:=isotropy u hu v hv
    have hvalue:Q v=Q u:=by rw [← hh];exact invariant h u
    have hscale:(gauge K x) • v=x:=by simp [v,smul_smul,hg.ne']
    calc
      Q x=Q ((gauge K x) • v):=congrArg Q hscale.symm
      _=Q u*(gauge K x)^2:=by rw [Q.map_smul,hvalue];simp [smul_eq_mul,pow_two,mul_comm]

theorem sr_isotropic_invariant_form_normalizes_to_full_body [Nontrivial E]
    (K : Set E) (closed : IsClosed K) (convex : Convex ℝ K)
    (zeroInterior : K∈𝓝 (0:E)) (bounded : Bornology.IsBounded K)
    {H : Type*} (rest : H → E ≃L[ℝ] E)
    (isotropy : ∀ x∈frontier K,∀ y∈frontier K,∃ h,rest h x=y)
    (Q : QuadraticForm ℝ E) (positive : Q.PosDef)
    (invariant : ∀ h x,Q (rest h x)=Q x) :
    ∃ G:QuadraticForm ℝ E,G.PosDef ∧
      (∀ x,G x=(gauge K x)^2) ∧ (∀ x,x∈K ↔ G x≤1) ∧
      ∀ h x,G (rest h x)=G x := by
  obtain ⟨c,hc,factor⟩:=sr_full_isotropy_fixes_quadratic_boundary_radius
    K convex zeroInterior bounded rest isotropy Q positive invariant
  refine ⟨c⁻¹ • Q,positive.smul (inv_pos.mpr hc),?_,?_,?_⟩
  · intro x
    change c⁻¹*Q x=(gauge K x)^2
    rw [factor,← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul]
  · intro x
    have hg:0≤gauge K x:=gauge_nonneg _
    have hmem:x∈K ↔ gauge K x≤1:=by
      simpa only [closed.closure_eq] using (gauge_le_one_iff_mem_closure convex zeroInterior).symm
    rw [hmem]
    change gauge K x≤1 ↔ c⁻¹*Q x≤1
    rw [factor,← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul]
    constructor <;> intro hh <;> nlinarith
  · intro h x
    change c⁻¹*Q (rest h x)=c⁻¹*Q x
    rw [invariant]

#print axioms sr_gauge_normalization_on_full_boundary
#print axioms sr_full_isotropy_fixes_quadratic_boundary_radius
#print axioms sr_isotropic_invariant_form_normalizes_to_full_body
end
end AASCMetricConstruction
