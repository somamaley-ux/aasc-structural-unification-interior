import KGNRFreeSSQ1

/-! A fixed full-space free scalar comparator class. Its inputs are generic
finite jets and a COMPLETE graph, not a Laplacian or generator identity.
The source Q9/Q10/free ledger are explicit; no paper-wide equivalence is claimed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory
open scoped SchwartzMap BigOperators
namespace AASCKleinGordon

structure KGScalarFreeComparator (H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert) where
  data : KGScalarDifferentialData
  response : 𝓢(KGSpatialSpace,ℂ) →L[ℂ] 𝓢(KGSpatialSpace,ℂ)
  response_data : ∀ f x,response f x = kgScalarJetResponse data f x
  complete_graph : ∀ f g,(f,g) ∈ H.graph ↔ ∀ test : 𝓢(KGSpatialSpace,ℂ),
    (g : KGSpatialDistribution) test = (f : KGSpatialDistribution) (response test)
  uniform_principal : ∃ c : ℝ,c ≠ 0 ∧ ∀ x i j,
    data.principal x i j = if i=j then (c : ℂ) else 0
  no_first : ∀ x i,data.first x i = 0
  free_zeroth : ∀ x,data.zeroth x = 0

def kgScalarFreeComparatorOfSSQ1 (a : Parameters)
    {H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert}
    (W : KGScalarSSQ1Witness a H (0 : KGSpatialSpace → ℝ)) : KGScalarFreeComparator H where
  data := W.data
  response := W.response
  response_data := W.response_data
  complete_graph := W.complete_graph
  uniform_principal := W.Q9_uniform_principal
  no_first := W.Q10_no_gauge
  free_zeroth x := by simpa using W.Q18_potential_ledger.1 x

theorem kg_free_comparator_response_normal_form
    {H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert}
    (C : KGScalarFreeComparator H) (c : ℝ)
    (principal : ∀ x i j,C.data.principal x i j = if i=j then (c : ℂ) else 0)
    (test : 𝓢(KGSpatialSpace,ℂ)) :
    C.response test = (c : ℂ) • kgSpatialLaplacian test := by
  ext x
  rw [C.response_data]
  simp [kgScalarJetResponse,C.free_zeroth,C.no_first,principal,
    kgSpatialLaplacian,Finset.mul_sum]

theorem kg_free_comparator_graph_of_principal
    {H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert}
    (C : KGScalarFreeComparator H) (c : ℝ)
    (principal : ∀ x i j,C.data.principal x i j = if i=j then (c : ℂ) else 0)
    (f g : KGNRSpatialHilbert) :
    (f,g) ∈ H.graph ↔ (g : KGSpatialDistribution) =
      (c : ℂ) • kgSpatialDistributionLaplacian (f : KGSpatialDistribution) := by
  rw [C.complete_graph]
  simp_rw [kg_free_comparator_response_normal_form C c principal]
  constructor
  · intro h
    ext test
    have ht := h test
    rw [map_smul] at ht
    change (g : KGSpatialDistribution) test = (c : ℂ) *
      kgSpatialDistributionLaplacian (f : KGSpatialDistribution) test
    rw [kg_spatial_distribution_laplacian_test]
    exact ht
  · intro h test
    have ht := congrArg (fun T : KGSpatialDistribution => T test) h
    change (g : KGSpatialDistribution) test = (c : ℂ) *
      kgSpatialDistributionLaplacian (f : KGSpatialDistribution) test at ht
    rw [kg_spatial_distribution_laplacian_test] at ht
    rw [map_smul]
    exact ht

theorem kg_free_comparator_complete_graph_normal_form
    {H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert}
    (C : KGScalarFreeComparator H) :
    ∃ c : ℝ,c ≠ 0 ∧
      (∀ test : 𝓢(KGSpatialSpace,ℂ),C.response test = (c : ℂ) • kgSpatialLaplacian test) ∧
      (∀ f g : KGNRSpatialHilbert,(f,g) ∈ H.graph ↔
        (g : KGSpatialDistribution) = (c : ℂ) •
          kgSpatialDistributionLaplacian (f : KGSpatialDistribution)) := by
  obtain ⟨c,hc,hp⟩ := C.uniform_principal
  exact ⟨c,hc,kg_free_comparator_response_normal_form C c hp,
    kg_free_comparator_graph_of_principal C c hp⟩

end AASCKleinGordon
