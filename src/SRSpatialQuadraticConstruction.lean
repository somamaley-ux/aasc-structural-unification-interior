import SRBodyCovarianceInvariant
import SRIsotropicBodyRadial

/-! Full compact-body construction in SR 5.7. The spatial form is an output:
covariance integration -> positive inverse -> actual rest invariance -> full
boundary isotropy -> normalized quadratic unit ball -> uniqueness.
The rest family may be arbitrary; no finite/compact/Lie group hypothesis is used.
Convexity, compactness, interior and actual isotropy remain source conditions. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
open Set
open scoped Matrix BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sr_positive_form_bound_from_full_unit_ball_inclusion
    (Q R : QuadraticForm ℝ E) (positive : Q.PosDef)
    (inclusion : ∀ x,Q x≤1 → R x≤1) (x : E) : R x≤Q x := by
  by_cases hx:x=0
  · simp [hx]
  · have hq:0<Q x:=positive x hx
    let a:ℝ:=Real.sqrt (Q x)
    have ha:0<a:=Real.sqrt_pos.mpr hq
    have haa:a*a=Q x:=Real.mul_self_sqrt hq.le
    have hy:Q (a⁻¹ • x)=1:=by
      rw [Q.map_smul]
      change (a⁻¹*a⁻¹)*Q x=1
      rw [← haa]
      field_simp
    have hr:=inclusion (a⁻¹ • x) hy.le
    rw [R.map_smul] at hr
    change (a⁻¹*a⁻¹)*R x≤1 at hr
    have hm:=mul_le_mul_of_nonneg_left hr (mul_pos ha ha).le
    have he:(a*a)*((a⁻¹*a⁻¹)*R x)=R x:=by field_simp
    rw [he,mul_one,haa] at hm
    exact hm

theorem sr_positive_quadratic_form_unique_from_full_unit_ball
    (Q R : QuadraticForm ℝ E) (hq : Q.PosDef) (hr : R.PosDef)
    (same : ∀ x,Q x≤1 ↔ R x≤1) : Q=R := by
  ext x
  exact le_antisymm
    (sr_positive_form_bound_from_full_unit_ball_inclusion R Q hr (fun x=>(same x).mpr) x)
    (sr_positive_form_bound_from_full_unit_ball_inclusion Q R hq (fun x=>(same x).mp) x)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def srCovarianceInverseQuadratic (K : Set (ι → ℝ)) : QuadraticForm ℝ (ι → ℝ):=
  ((srBodyCovariance K)⁻¹).toQuadraticMap'

theorem sr_matrix_quadratic_value (M : Matrix ι ι ℝ) (x : ι → ℝ) :
    M.toQuadraticMap' x=x ⬝ᵥ M *ᵥ x := by
  simp only [Matrix.toQuadraticMap',LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply']

theorem sr_matrix_quadratic_congruence (M A : Matrix ι ι ℝ) (x : ι → ℝ) :
    (A.transpose*M*A).toQuadraticMap' x=M.toQuadraticMap' (A *ᵥ x) := by
  simp only [sr_matrix_quadratic_value]
  calc
    _=x ⬝ᵥ A.transpose *ᵥ (M *ᵥ (A *ᵥ x)) := by
      simp only [Matrix.mulVec_mulVec,Matrix.mul_assoc]
    _=(A *ᵥ x) ⬝ᵥ M *ᵥ (A *ᵥ x) := by
      rw [Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]

theorem sr_constructed_covariance_inverse_positive (K : Set (ι → ℝ))
    (compact : IsCompact K) (zeroInterior : K∈𝓝 (0:ι → ℝ)) :
    (srCovarianceInverseQuadratic K).PosDef :=
  (sr_body_covariance_positive_definite K compact zeroInterior).inv.toQuadraticForm'

theorem sr_constructed_covariance_inverse_rest_invariant
    (K : Set (ι → ℝ)) (compact : IsCompact K) (zeroInterior : K∈𝓝 (0:ι → ℝ))
    (h : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (preserves : h '' K=K) (x : ι → ℝ) :
    srCovarianceInverseQuadratic K (h x)=srCovarianceInverseQuadratic K x := by
  change ((srBodyCovariance K)⁻¹).toQuadraticMap' (h x)=
    ((srBodyCovariance K)⁻¹).toQuadraticMap' x
  rw [← sr_rest_matrix_applies h x,← sr_matrix_quadratic_congruence,
    sr_covariance_inverse_congruence_invariant K compact zeroInterior h preserves]

theorem sr_full_body_isotropy_constructs_unique_spatial_quadratic_form [Nontrivial (ι → ℝ)]
    (K : Set (ι → ℝ)) (compact : IsCompact K) (convex : Convex ℝ K)
    (zeroInterior : K∈𝓝 (0:ι → ℝ)) {H : Type*}
    (rest : H → (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    (preserves : ∀ h,rest h '' K=K)
    (isotropy : ∀ x∈frontier K,∀ y∈frontier K,∃ h,rest h x=y) :
    ∃! G:QuadraticForm ℝ (ι → ℝ),G.PosDef ∧
      (∀ x,x∈K ↔ G x≤1) ∧ (∀ h x,G (rest h x)=G x) ∧
      ∀ x,G x=(gauge K x)^2 := by
  obtain ⟨G,hpos,hgauge,hbody,hinv⟩:=sr_isotropic_invariant_form_normalizes_to_full_body
    K compact.isClosed convex zeroInterior compact.isBounded rest isotropy
    (srCovarianceInverseQuadratic K)
    (sr_constructed_covariance_inverse_positive K compact zeroInterior)
    (fun h=>sr_constructed_covariance_inverse_rest_invariant K compact zeroInterior (rest h) (preserves h))
  refine ⟨G,⟨hpos,hbody,hinv,hgauge⟩,?_⟩
  intro other ho
  apply sr_positive_quadratic_form_unique_from_full_unit_ball other G ho.1 hpos
  intro x
  exact (ho.2.1 x).symm.trans (hbody x)

#print axioms sr_positive_form_bound_from_full_unit_ball_inclusion
#print axioms sr_positive_quadratic_form_unique_from_full_unit_ball
#print axioms sr_matrix_quadratic_value
#print axioms sr_matrix_quadratic_congruence
#print axioms sr_constructed_covariance_inverse_positive
#print axioms sr_constructed_covariance_inverse_rest_invariant
#print axioms sr_full_body_isotropy_constructs_unique_spatial_quadratic_form
end
end AASCMetricConstruction
