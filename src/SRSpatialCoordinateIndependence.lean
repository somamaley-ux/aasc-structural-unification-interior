import SRSpatialQuadraticConstruction
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! SR 5.7 on any finite-dimensional real normed presentation. Auxiliary
coordinates are constructed from a basis, not physical metric inputs. The
full-unit-ball uniqueness theorem proves independence of that choice. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

theorem sr_arbitrary_finite_dimensional_isotropic_body_constructs_unique_form
    (K : Set E) (compact : IsCompact K) (convex : Convex ℝ K)
    (zeroInterior : K∈𝓝 (0:E)) {H : Type*} (rest : H → E ≃L[ℝ] E)
    (preserves : ∀ h,rest h '' K=K)
    (isotropy : ∀ x∈frontier K,∀ y∈frontier K,∃ h,rest h x=y) :
    ∃! G:QuadraticForm ℝ E,G.PosDef ∧ (∀ x,x∈K ↔ G x≤1) ∧
      ∀ h x,G (rest h x)=G x := by
  let coord:E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ):=(Module.finBasis ℝ E).equivFunL
  letI:Nontrivial (Fin (Module.finrank ℝ E) → ℝ):=by
    obtain ⟨x,y,hxy⟩:=exists_pair_ne E
    exact ⟨⟨coord x,coord y,fun he=>hxy (coord.injective he)⟩⟩
  let K':Set (Fin (Module.finrank ℝ E) → ℝ):=coord '' K
  let rest':H → (Fin (Module.finrank ℝ E) → ℝ) ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ):=
    fun h=>coord.symm.trans ((rest h).trans coord)
  have hkcompact:IsCompact K':=compact.image coord.continuous
  have hkconvex:Convex ℝ K':=convex.linear_image coord.toLinearMap
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
  have hfront:coord '' frontier K=frontier K':=coord.toHomeomorph.image_frontier K
  have hkisotropy:∀ x∈frontier K',∀ y∈frontier K',∃ h,rest' h x=y:=by
    intro x hx y hy
    rw [← hfront] at hx hy
    obtain ⟨u,hu,rfl⟩:=hx
    obtain ⟨v,hv,rfl⟩:=hy
    obtain ⟨h,he⟩:=isotropy u hu v hv
    exact ⟨h,by simp [rest',he]⟩
  obtain ⟨Q,hQ,_⟩:=sr_full_body_isotropy_constructs_unique_spatial_quadratic_form
    K' hkcompact hkconvex hkzero rest' hkpreserve hkisotropy
  let G:QuadraticForm ℝ E:=Q.comp coord.toLinearMap
  have hgpositive:G.PosDef:=by
    intro x hx
    apply hQ.1
    intro he
    apply hx
    apply coord.injective
    simpa only [map_zero] using he
  have hgbody (x:E):x∈K ↔ G x≤1:=by
    have hm:coord x∈K' ↔ x∈K:=by
      change coord x∈coord '' K ↔ x∈K
      exact coord.injective.mem_set_image
    exact hm.symm.trans (hQ.2.1 (coord x))
  have hginv (h:H) (x:E):G (rest h x)=G x:=by
    have he:=hQ.2.2.1 h (coord x)
    simpa [G,rest'] using he
  refine ⟨G,⟨hgpositive,hgbody,hginv⟩,?_⟩
  intro other ho
  apply sr_positive_quadratic_form_unique_from_full_unit_ball other G ho.1 hgpositive
  intro x
  exact (ho.2.1 x).symm.trans (hgbody x)

#print axioms sr_arbitrary_finite_dimensional_isotropic_body_constructs_unique_form
end
end AASCMetricConstruction
