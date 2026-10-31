import KGNREuclideanScalar
import KGNRScalarNontrivial

/-! A free-instance translation of the nineteen independent source clauses.
Finite-jet data and a complete weak graph are witnesses, not assumptions of the
desired Schrodinger equation. No comparison-class exhaustion is asserted. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Filter LineDeriv Laplacian
open scoped SchwartzMap Topology
namespace AASCKleinGordon

def kgNRTestResponseCLM (a : Parameters) :
    𝓢(KGSpatialSpace,ℂ) →L[ℂ] 𝓢(KGSpatialSpace,ℂ) :=
  (kgNRPrincipalCoefficient a : ℂ) • laplacianCLM ℂ KGSpatialSpace 𝓢(KGSpatialSpace,ℂ)

theorem kg_nr_test_response_clm (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) :
    kgNRTestResponseCLM a f = kgNRSpatialTestResponse a f := by
  rw [kgNRTestResponseCLM,ContinuousLinearMap.smul_apply,SchwartzMap.laplacianCLM_eq,
    kg_spatial_schwartz_laplacian_intrinsic]
  rfl

theorem kg_nr_spatial_group_zero (a : Parameters) (f : KGNRSpatialHilbert) :
    kgNRSpatialFreeFlow a 0 f = f := by
  change kgPhysicalSpatialUnitary a
    (kgNRFreeMomentumFlow a 0 ((kgPhysicalSpatialUnitary a).symm f)) = f
  rw [show kgNRFreeMomentumFlow a 0 ((kgPhysicalSpatialUnitary a).symm f) =
      (kgPhysicalSpatialUnitary a).symm f from
    Multiplication.phaseMultiplier_zero (kgNRKineticEnergy a) (kg_nr_kinetic_measurable a) a.hbar _]
  exact (kgPhysicalSpatialUnitary a).apply_symm_apply f

theorem kg_nr_spatial_group_add (a : Parameters) (t s : ℝ) (f : KGNRSpatialHilbert) :
    kgNRSpatialFreeFlow a (t+s) f = kgNRSpatialFreeFlow a t (kgNRSpatialFreeFlow a s f) := by
  change kgPhysicalSpatialUnitary a
    (kgNRFreeMomentumFlow a (t+s) ((kgPhysicalSpatialUnitary a).symm f)) =
    kgPhysicalSpatialUnitary a (kgNRFreeMomentumFlow a t
      ((kgPhysicalSpatialUnitary a).symm (kgPhysicalSpatialUnitary a
        (kgNRFreeMomentumFlow a s ((kgPhysicalSpatialUnitary a).symm f)))))
  rw [(kgPhysicalSpatialUnitary a).symm_apply_apply,kg_nr_free_momentum_flow_add]

structure KGClosedScalarEvolution (a : Parameters)
    (H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert) where
  flow : ℝ → KGNRSpatialHilbert ≃ₗᵢ[ℂ] KGNRSpatialHilbert
  zero : ∀ f,flow 0 f = f
  add : ∀ t s f,flow (t+s) f = flow t (flow s f)
  strong : ∀ f,Continuous (fun t => flow t f)
  generator : ∀ f : H.domain,HasDerivAt (fun t => flow t f.val)
    (Translation.coefficient a.hbar • H f) 0

def kgNRConstructedEvolution (a : Parameters) : KGClosedScalarEvolution a (kgNRSpatialKinetic a) where
  flow := kgNRSpatialFreeFlow a
  zero := kg_nr_spatial_group_zero a
  add := kg_nr_spatial_group_add a
  strong f := (kgPhysicalSpatialUnitary a).continuous.comp
    (kg_nr_free_momentum_flow_continuous a ((kgPhysicalSpatialUnitary a).symm f))
  generator := kg_nr_spatial_free_flow_generator a

def kgNRPotentialOperator (V : KGSpatialSpace → ℝ) :
    KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert := Multiplication.realMultiplication V

theorem kg_nr_zero_potential_graph (f g : KGNRSpatialHilbert) :
    (f,g) ∈ (kgNRPotentialOperator (0 : KGSpatialSpace → ℝ)).graph ↔ g = 0 := by
  rw [kgNRPotentialOperator,Multiplication.realMultiplication_mem_graph]
  constructor
  · intro h
    apply Lp.ext
    filter_upwards [h,Lp.coeFn_zero ℂ 2 (volume : Measure KGSpatialSpace)] with x hx hz
    change g x = (0 : KGNRSpatialHilbert) x
    simpa only [Pi.zero_apply,Complex.ofReal_zero,zero_mul,hz] using hx
  · rintro rfl
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure KGSpatialSpace)] with x hx
    simpa only [Pi.zero_apply,Complex.ofReal_zero,zero_mul] using hx

theorem kg_nr_zero_potential_domain (f : KGNRSpatialHilbert) :
    f ∈ (kgNRPotentialOperator (0 : KGSpatialSpace → ℝ)).domain :=
  LinearPMap.mem_domain_of_mem_graph ((kg_nr_zero_potential_graph f 0).mpr rfl)

theorem kg_nr_zero_potential_sum_graph (a : Parameters) (f g : KGNRSpatialHilbert) :
    (f,g) ∈ (kgNRSpatialKinetic a).graph ↔
      ∃ k v : KGNRSpatialHilbert,(f,k) ∈ (kgNRSpatialKinetic a).graph ∧
        (f,v) ∈ (kgNRPotentialOperator (0 : KGSpatialSpace → ℝ)).graph ∧ g = k+v := by
  constructor
  · intro h
    exact ⟨g,0,h,(kg_nr_zero_potential_graph f 0).mpr rfl,(add_zero g).symm⟩
  · rintro ⟨k,v,hk,hv,hg⟩
    rw [(kg_nr_zero_potential_graph f v).mp hv,add_zero] at hg
    simpa only [hg] using hk

/-- Generic finite scalar differential data are deliberately not fixed to a
Laplacian. The Q-fields preserve the source clause numbering and free receiving
meaning. Their complete graph witness rules out extra operator load. -/
structure KGScalarSSQ1Witness (a : Parameters)
    (H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert) (V : KGSpatialSpace → ℝ) where
  data : KGScalarDifferentialData
  response : 𝓢(KGSpatialSpace,ℂ) →L[ℂ] 𝓢(KGSpatialSpace,ℂ)
  response_data : ∀ f x,response f x = kgScalarJetResponse data f x
  complete_graph : ∀ f g,(f,g) ∈ H.graph ↔ ∀ test : 𝓢(KGSpatialSpace,ℂ),
    (g : KGSpatialDistribution) test = (f : KGSpatialDistribution) (response test)
  evolution : KGClosedScalarEvolution a H
  Q1_hilbert_internal : ∃ k : Momentum → ℝ,
    H.graph = (AASCSpatial.unitaryTransport (kgPhysicalSpatialUnitary a)
      (Multiplication.realMultiplication k)).graph
  Q2_dense_domain : Dense (H.domain : Set KGNRSpatialHilbert)
  Q3_self_adjoint : IsSelfAdjoint H
  Q4_linear : ∀ f g : H.domain,H (f+g) = H f + H g
  Q5_projective : ∀ (c : ℂ) (f : H.domain),H (c • f) = c • H f
  Q6_local : ∀ (f g : 𝓢(KGSpatialSpace,ℂ)) x,(f : KGSpatialSpace → ℂ) =ᶠ[𝓝 x] g → response f x = response g x
  Q7_euclidean :
    (∀ (R : KGSpatialSpace ≃ₗᵢ[ℝ] KGSpatialSpace) f g,(f,g) ∈ H.graph →
      (kgNRSpatialRotation R f,kgNRSpatialRotation R g) ∈ H.graph) ∧
    (∀ (b : KGSpatialSpace) f g,(f,g) ∈ H.graph →
      (kgNRSpatialTranslation b f,kgNRSpatialTranslation b g) ∈ H.graph)
  Q8_order : ∀ f g x,KGScalarSameTwoJet f g x → response f x = response g x
  Q9_uniform_principal : ∃ c : ℝ,c ≠ 0 ∧ ∀ x i j,
    data.principal x i j = if i=j then (c : ℂ) else 0
  Q10_no_gauge : ∀ x i,data.first x i = 0
  Q11_scalar_fibre : Module.finrank ℂ ℂ = 1
  Q12_spatial_only : ∀ (f : ℝ → 𝓢(KGSpatialSpace,ℂ)) t x,
    response (f t) x = kgScalarJetResponse data (f t) x
  Q13_no_nonlinearity : ∀ (c : ℂ) (f g : 𝓢(KGSpatialSpace,ℂ)),response (c • f+g) = c • response f + response g
  Q14_closed_norm : ∀ t f,‖evolution.flow t f‖ = ‖f‖
  Q15_no_update : ∀ t,Function.Bijective (evolution.flow t)
  Q16_no_nonlocal : ∀ f g x,KGScalarSameTwoJet f g x → response f x = response g x
  Q17_maximal_full_space_domain : ∀ f,f ∈ H.domain ↔ ∃ g : KGNRSpatialHilbert,
    ∀ test : 𝓢(KGSpatialSpace,ℂ),
      (g : KGSpatialDistribution) test = (f : KGSpatialDistribution) (response test)
  Q18_potential_ledger : (∀ x,data.zeroth x = (V x : ℂ)) ∧
    (∀ f g,(f,g) ∈ (kgNRPotentialOperator V).graph ↔
      g =ᵐ[volume] (fun x => (V x : ℂ)*f x))
  Q19_nontrivial : ∀ c : ℂ,∃ f : H.domain,H f ≠ c • f.val

def SameScopeQuantumSpatial1 (a : Parameters)
    (H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert) (V : KGSpatialSpace → ℝ) : Prop :=
  Nonempty (KGScalarSSQ1Witness a H V)

def kgNRFreeSSQ1Witness (a : Parameters) :
    KGScalarSSQ1Witness a (kgNRSpatialKinetic a) (0 : KGSpatialSpace → ℝ) where
  data := kgNRFreeDifferentialData a
  response := kgNRTestResponseCLM a
  response_data f x := (congrArg (fun g : 𝓢(KGSpatialSpace,ℂ) => g x)
    (kg_nr_test_response_clm a f)).trans (kg_nr_free_response_data a f x).symm
  complete_graph f g := by simpa only [kg_nr_test_response_clm] using kg_nr_spatial_kinetic_test_graph a f g
  evolution := kgNRConstructedEvolution a
  Q1_hilbert_internal := ⟨kgNRKineticEnergy a,rfl⟩
  Q2_dense_domain := kg_nr_spatial_kinetic_dense a
  Q3_self_adjoint := kg_nr_spatial_kinetic_self_adjoint a
  Q4_linear f g := map_add _ f g
  Q5_projective c f := map_smul _ c f
  Q6_local f g x h := by simpa only [kg_nr_test_response_clm] using kg_nr_free_test_response_local a f g x h
  Q7_euclidean := ⟨kg_nr_spatial_rotation_graph a,kg_nr_spatial_translation_graph a⟩
  Q8_order f g x h := by
    simpa only [kg_nr_test_response_clm,← kg_nr_free_response_data] using
      kg_scalar_response_two_jet (kgNRFreeDifferentialData a) f g x h
  Q9_uniform_principal := kg_nr_free_response_principal a
  Q10_no_gauge := (kg_nr_free_no_first_or_potential a).2
  Q11_scalar_fibre := Module.finrank_self ℂ
  Q12_spatial_only f t x := (congrArg (fun g : 𝓢(KGSpatialSpace,ℂ) => g x)
    (kg_nr_test_response_clm a (f t))).trans (kg_nr_free_response_data a (f t) x).symm
  Q13_no_nonlinearity c f g := by rw [map_add,map_smul]
  Q14_closed_norm t f := (kgNRSpatialFreeFlow a t).norm_map f
  Q15_no_update t := (kgNRSpatialFreeFlow a t).bijective
  Q16_no_nonlocal f g x h := by
    simpa only [kg_nr_test_response_clm,← kg_nr_free_response_data] using
      kg_scalar_response_two_jet (kgNRFreeDifferentialData a) f g x h
  Q17_maximal_full_space_domain f := by
    constructor
    · intro hf
      exact ⟨kgNRSpatialKinetic a ⟨f,hf⟩,by
        simpa only [kg_nr_test_response_clm] using
          (kg_nr_spatial_kinetic_test_graph a f _).mp ((kgNRSpatialKinetic a).mem_graph ⟨f,hf⟩)⟩
    · rintro ⟨g,hg⟩
      exact LinearPMap.mem_domain_of_mem_graph ((kg_nr_spatial_kinetic_test_graph a f g).mpr
        (by simpa only [kg_nr_test_response_clm] using hg))
  Q18_potential_ledger := ⟨fun _ => rfl,Multiplication.realMultiplication_mem_graph _⟩
  Q19_nontrivial := kg_nr_spatial_generator_not_homogeneous a

theorem kg_nr_free_ssq1 (a : Parameters) :
    SameScopeQuantumSpatial1 a (kgNRSpatialKinetic a) (0 : KGSpatialSpace → ℝ) :=
  ⟨kgNRFreeSSQ1Witness a⟩

end AASCKleinGordon
