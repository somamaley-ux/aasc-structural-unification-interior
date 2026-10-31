import KGNRSourceKineticCore

/-! Independent finite-jet response data, locality and principal tensor.
These conditions concern an actual differential response on tests; none is
defined as a desired Hamiltonian equality. The graph comparison is proved. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Filter LineDeriv Laplacian
open scoped SchwartzMap BigOperators Topology
namespace AASCKleinGordon

structure KGScalarDifferentialData where
  zeroth : KGSpatialSpace → ℂ
  first : KGSpatialSpace → Fin 3 → ℂ
  principal : KGSpatialSpace → Fin 3 → Fin 3 → ℂ

def kgScalarJetResponse (D : KGScalarDifferentialData)
    (f : 𝓢(KGSpatialSpace,ℂ)) (x : KGSpatialSpace) : ℂ :=
  D.zeroth x * f x + ∑ i, D.first x i * kgSpatialPartialCLM i f x +
    ∑ i, ∑ j, D.principal x i j * kgSpatialPartialCLM i (kgSpatialPartialCLM j f) x

def KGScalarSameTwoJet (f g : 𝓢(KGSpatialSpace,ℂ)) (x : KGSpatialSpace) : Prop :=
  f x = g x ∧ (∀ i,kgSpatialPartialCLM i f x = kgSpatialPartialCLM i g x) ∧
    ∀ i j,kgSpatialPartialCLM i (kgSpatialPartialCLM j f) x =
      kgSpatialPartialCLM i (kgSpatialPartialCLM j g) x

theorem kg_scalar_response_two_jet (D : KGScalarDifferentialData)
    (f g : 𝓢(KGSpatialSpace,ℂ)) (x : KGSpatialSpace) (h : KGScalarSameTwoJet f g x) :
    kgScalarJetResponse D f x = kgScalarJetResponse D g x := by
  unfold kgScalarJetResponse
  rw [h.1]
  simp_rw [h.2.1,h.2.2]

theorem kg_scalar_same_two_jet_of_germ (f g : 𝓢(KGSpatialSpace,ℂ))
    (x : KGSpatialSpace) (h : (f : KGSpatialSpace → ℂ) =ᶠ[𝓝 x] g) :
    KGScalarSameTwoJet f g x := by
  refine ⟨h.eq_of_nhds,?_,?_⟩
  · intro i
    exact congrArg (fun L : KGSpatialSpace →L[ℝ] ℂ => L (kgSpatialDirection i))
      (h.fderiv (𝕜 := ℝ)).eq_of_nhds
  · intro i j
    have hj : (kgSpatialPartialCLM j f : KGSpatialSpace → ℂ) =ᶠ[𝓝 x]
        kgSpatialPartialCLM j g := by
      filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
      exact congrArg (fun L : KGSpatialSpace →L[ℝ] ℂ => L (kgSpatialDirection j)) hy
    exact congrArg (fun L : KGSpatialSpace →L[ℝ] ℂ => L (kgSpatialDirection i))
      (hj.fderiv (𝕜 := ℝ)).eq_of_nhds

theorem kg_scalar_response_local (D : KGScalarDifferentialData)
    (f g : 𝓢(KGSpatialSpace,ℂ)) (x : KGSpatialSpace)
    (h : (f : KGSpatialSpace → ℂ) =ᶠ[𝓝 x] g) :
    kgScalarJetResponse D f x = kgScalarJetResponse D g x :=
  kg_scalar_response_two_jet D f g x (kg_scalar_same_two_jet_of_germ f g x h)

def kgNRPrincipalCoefficient (a : Parameters) : ℝ := -(a.hbar^2/(2*a.mass))

def kgNRFreeDifferentialData (a : Parameters) : KGScalarDifferentialData where
  zeroth _ := 0
  first _ _ := 0
  principal _ i j := if i = j then (kgNRPrincipalCoefficient a : ℂ) else 0

def kgNRSpatialTestResponse (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) :
    𝓢(KGSpatialSpace,ℂ) := (kgNRPrincipalCoefficient a : ℂ) • kgSpatialLaplacian f

theorem kg_nr_free_response_data (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ))
    (x : KGSpatialSpace) :
    kgScalarJetResponse (kgNRFreeDifferentialData a) f x = kgNRSpatialTestResponse a f x := by
  simp [kgScalarJetResponse,kgNRFreeDifferentialData,kgNRSpatialTestResponse,
    kgSpatialLaplacian,Finset.mul_sum]

theorem kg_nr_free_test_response_local (a : Parameters) (f g : 𝓢(KGSpatialSpace,ℂ))
    (x : KGSpatialSpace) (h : (f : KGSpatialSpace → ℂ) =ᶠ[𝓝 x] g) :
    kgNRSpatialTestResponse a f x = kgNRSpatialTestResponse a g x := by
  rw [← kg_nr_free_response_data,← kg_nr_free_response_data]
  exact kg_scalar_response_local _ f g x h

theorem kg_nr_principal_coefficient_negative (a : Parameters) : kgNRPrincipalCoefficient a < 0 := by
  unfold kgNRPrincipalCoefficient
  exact neg_neg_of_pos (div_pos (sq_pos_of_pos a.hbar_pos) (mul_pos (by norm_num) a.mass_pos))

theorem kg_nr_free_response_principal (a : Parameters) :
    ∃ c : ℝ,c ≠ 0 ∧ ∀ (x : KGSpatialSpace) (i j : Fin 3),
      (kgNRFreeDifferentialData a).principal x i j = if i=j then (c : ℂ) else 0 :=
  ⟨kgNRPrincipalCoefficient a,(kg_nr_principal_coefficient_negative a).ne,fun _ _ _ => rfl⟩

theorem kg_nr_free_no_first_or_potential (a : Parameters) :
    (∀ x,(kgNRFreeDifferentialData a).zeroth x = 0) ∧
    (∀ x i,(kgNRFreeDifferentialData a).first x i = 0) := ⟨fun _ => rfl,fun _ _ => rfl⟩

theorem kg_nr_spatial_kinetic_test_graph (a : Parameters) (f g : KGNRSpatialHilbert) :
    (f,g) ∈ (kgNRSpatialKinetic a).graph ↔
      ∀ test : 𝓢(KGSpatialSpace,ℂ),
        (g : KGSpatialDistribution) test = (f : KGSpatialDistribution) (kgNRSpatialTestResponse a test) := by
  rw [kg_nr_spatial_kinetic_weak_graph]
  unfold kgSpatialWeakKineticGraph
  have hc : (-(a.hbar ^ 2 / (2 * a.mass)) : ℂ) = (kgNRPrincipalCoefficient a : ℂ) := by
    unfold kgNRPrincipalCoefficient
    push_cast
    rfl
  rw [hc]
  constructor
  · intro h test
    have ht := congrArg (fun T : KGSpatialDistribution => T test) h
    change (g : KGSpatialDistribution) test = (kgNRPrincipalCoefficient a : ℂ) *
      kgSpatialDistributionLaplacian (f : KGSpatialDistribution) test at ht
    rw [kg_spatial_distribution_laplacian_test] at ht
    change (g : KGSpatialDistribution) test = (f : KGSpatialDistribution)
      ((kgNRPrincipalCoefficient a : ℂ) • kgSpatialLaplacian test)
    rw [map_smul]
    exact ht
  · intro h
    ext test
    have ht := h test
    change (g : KGSpatialDistribution) test = (f : KGSpatialDistribution)
      ((kgNRPrincipalCoefficient a : ℂ) • kgSpatialLaplacian test) at ht
    rw [map_smul] at ht
    change (g : KGSpatialDistribution) test = (kgNRPrincipalCoefficient a : ℂ) *
      kgSpatialDistributionLaplacian (f : KGSpatialDistribution) test
    rw [kg_spatial_distribution_laplacian_test]
    exact ht

end AASCKleinGordon
