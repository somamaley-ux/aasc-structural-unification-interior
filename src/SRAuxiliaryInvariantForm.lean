import SRSpatialQuadraticConstruction
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.FunProp

/-! Auxiliary invariant quadratic form constructed from an actual compact
zero-neighborhood. No transitivity, group compactness or invariant form is input.
This form is a proof instrument for clock separation, not the physical ruler. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open Set
open scoped Topology Matrix BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

theorem sr_compact_original_body_constructs_invariant_auxiliary_form
    (K : Set E) (compact : IsCompact K) (zeroInterior : K∈𝓝 (0:E))
    {H : Type*} (rest : H → E ≃L[ℝ] E) (preserves : ∀ h,rest h '' K=K) :
    ∃ Q:QuadraticForm ℝ E,Q.PosDef ∧ Continuous Q ∧ ∀ h x,Q (rest h x)=Q x := by
  let coord:E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ):=(Module.finBasis ℝ E).equivFunL
  letI:Nontrivial (Fin (Module.finrank ℝ E) → ℝ):=by
    obtain ⟨x,y,hxy⟩:=exists_pair_ne E
    exact ⟨⟨coord x,coord y,fun he=>hxy (coord.injective he)⟩⟩
  let K':Set (Fin (Module.finrank ℝ E) → ℝ):=coord '' K
  let rest':H → (Fin (Module.finrank ℝ E) → ℝ) ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ):=
    fun h=>coord.symm.trans ((rest h).trans coord)
  have hkcompact:IsCompact K':=compact.image coord.continuous
  have hkzero:K'∈𝓝 0:=by
    apply mem_interior_iff_mem_nhds.mp
    change 0∈interior (coord.toHomeomorph '' K)
    rw [← coord.toHomeomorph.image_interior K]
    exact ⟨0,mem_interior_iff_mem_nhds.mpr zeroInterior,map_zero coord⟩
  have hkpreserve (h:H):rest' h '' K'=K':=by
    ext y
    constructor
    · rintro ⟨z,⟨x,hx,rfl⟩,rfl⟩
      refine ⟨rest h x,?_,?_⟩
      · have hm:rest h x∈rest h '' K:=⟨x,hx,rfl⟩
        rw [preserves h] at hm
        exact hm
      · simp [rest']
    · rintro ⟨x,hx,rfl⟩
      have hm:x∈rest h '' K:=by rw [preserves h];exact hx
      obtain ⟨z,hz,he⟩:=hm
      refine ⟨coord z,⟨z,hz,rfl⟩,?_⟩
      simp [rest',he]
  let Q:QuadraticForm ℝ E:=(srCovarianceInverseQuadratic K').comp coord.toLinearMap
  have hp:Q.PosDef:=by
    intro x hx
    apply sr_constructed_covariance_inverse_positive K' hkcompact hkzero
    intro he
    apply hx
    apply coord.injective
    simpa only [map_zero] using he
  refine ⟨Q,hp,?_,?_⟩
  · change Continuous fun x:E=>(srCovarianceInverseQuadratic K') (coord x)
    simp only [srCovarianceInverseQuadratic,sr_matrix_quadratic_value,dotProduct,
      Matrix.mulVec,dotProduct]
    fun_prop
  · intro h x
    have hi:=sr_constructed_covariance_inverse_rest_invariant K' hkcompact hkzero
      (rest' h) (hkpreserve h) (coord x)
    simpa [Q,rest'] using hi

#print axioms sr_compact_original_body_constructs_invariant_auxiliary_form
end
end AASCMetricConstruction
