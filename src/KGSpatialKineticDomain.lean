import KGSpatialWeakLaplacian
import UnitaryUnboundedTransport

/-! Physical spatial kinetic operator, with full graph and weak domain comparison. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped FourierTransform SchwartzMap Topology
namespace AASCKleinGordon

theorem kg_unitary_transport_graph
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : H ≃ₗᵢ[ℂ] K) (T : H →ₗ.[ℂ] H) (f g : K) :
    (f,g) ∈ (AASCSpatial.unitaryTransport U T).graph ↔
      (U.symm f,U.symm g) ∈ T.graph := by
  constructor
  · intro h
    obtain ⟨y,hy⟩ := (LinearPMap.mem_graph_iff' _).mp h
    cases hy
    simpa only [AASCSpatial.unitaryTransport_apply, U.symm_apply_apply] using
      T.mem_graph ⟨U.symm y.val,y.prop⟩
  · intro h
    obtain ⟨x,hx,hg⟩ := (LinearPMap.mem_graph_iff _).mp h
    have ht := (AASCSpatial.unitaryTransport U T).mem_graph
      (AASCSpatial.unitaryTransportOriginal U T x)
    change (U x.val, AASCSpatial.unitaryTransport U T
      (AASCSpatial.unitaryTransportOriginal U T x)) ∈ _ at ht
    rw [AASCSpatial.unitaryTransport_on_original] at ht
    simpa only [hx, hg, U.apply_symm_apply] using ht

theorem kg_physical_frequency_graph (a : Parameters) (f g : KGNRMomentumHilbert) :
    (kgPhysicalFrequencyUnitary a f,kgPhysicalFrequencyUnitary a g) ∈
        (Multiplication.realMultiplication (kgNRFrequencyKineticEnergy a)).graph ↔
      (f,g) ∈ (kgNRFreeMomentumGenerator a).graph := by
  rw [Multiplication.realMultiplication_mem_graph,
    kgNRFreeMomentumGenerator, Multiplication.realMultiplication_mem_graph]
  have he := kg_physical_momentum_measure_preserving a
  have hr : (kgPhysicalMomentumRoot a : ℂ) ≠ 0 := by
    exact_mod_cast (kg_physical_momentum_root_positive a).ne'
  constructor
  · intro h
    have hp : (fun x : KGSpatialSpace => g (kgPhysicalMomentumME a x)) =ᵐ[volume]
        (fun x => (kgNRKineticEnergy a (kgPhysicalMomentumME a x) : ℂ) *
          f (kgPhysicalMomentumME a x)) := by
      filter_upwards [h,kg_physical_frequency_unitary_ae a f,
        kg_physical_frequency_unitary_ae a g] with x hx hf hg
      rw [hf,hg] at hx
      change (kgPhysicalMomentumRoot a : ℂ) * g (kgPhysicalMomentumME a x) =
        (kgNRKineticEnergy a (kgPhysicalMomentumME a x) : ℂ) *
          ((kgPhysicalMomentumRoot a : ℂ) * f (kgPhysicalMomentumME a x)) at hx
      apply mul_left_cancel₀ hr
      calc
        _ = _ := hx
        _ = _ := by ring
    have hi := MeasurePreserving.symm (kgPhysicalMomentumME a) he
    apply (kg_physical_momentum_ae a).mp
    simpa only [Function.comp_apply, MeasurableEquiv.apply_symm_apply] using
      hi.quasiMeasurePreserving.ae hp
  · intro h
    have hp := he.quasiMeasurePreserving.ae ((kg_physical_momentum_ae a).mpr h)
    filter_upwards [hp,kg_physical_frequency_unitary_ae a f,
      kg_physical_frequency_unitary_ae a g] with x hx hf hg
    rw [hf,hg]
    change (kgPhysicalMomentumRoot a : ℂ) * g (kgPhysicalMomentumME a x) =
      (kgNRKineticEnergy a (kgPhysicalMomentumME a x) : ℂ) *
        ((kgPhysicalMomentumRoot a : ℂ) * f (kgPhysicalMomentumME a x))
    rw [hx]
    ring

def kgNRSpatialKinetic (a : Parameters) : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert :=
  AASCSpatial.unitaryTransport (kgPhysicalSpatialUnitary a) (kgNRFreeMomentumGenerator a)

theorem kg_nr_spatial_kinetic_self_adjoint (a : Parameters) :
    IsSelfAdjoint (kgNRSpatialKinetic a) :=
  AASCSpatial.unitaryTransport_selfAdjoint _ _ (kg_nr_free_momentum_generator_self_adjoint a)

theorem kg_nr_spatial_kinetic_dense (a : Parameters) :
    Dense ((kgNRSpatialKinetic a).domain : Set KGNRSpatialHilbert) :=
  AASCSpatial.unitaryTransport_dense _ _ (kg_nr_free_momentum_generator_dense a)

theorem kg_nr_spatial_kinetic_fourier_graph (a : Parameters) (f g : KGNRSpatialHilbert) :
    (f,g) ∈ (kgNRSpatialKinetic a).graph ↔
      (𝓕 f,𝓕 g) ∈ (Multiplication.realMultiplication (kgNRFrequencyKineticEnergy a)).graph := by
  rw [kgNRSpatialKinetic, kg_unitary_transport_graph, ← kg_physical_frequency_graph]
  have hf := kg_physical_spatial_fourier a ((kgPhysicalSpatialUnitary a).symm f)
  have hg := kg_physical_spatial_fourier a ((kgPhysicalSpatialUnitary a).symm g)
  simp only [LinearIsometryEquiv.apply_symm_apply] at hf hg
  rw [← hf,← hg]

theorem kg_nr_spatial_kinetic_maximal_domain (a : Parameters) (f : KGNRSpatialHilbert) :
    f ∈ (kgNRSpatialKinetic a).domain ↔
      MemLp (fun ξ => (kgNRFrequencyKineticEnergy a ξ : ℂ) * (𝓕 f) ξ) 2 volume := by
  rw [← Multiplication.realMultiplication_exact_domain]
  constructor
  · intro h
    exact LinearPMap.mem_domain_of_mem_graph
      ((kg_nr_spatial_kinetic_fourier_graph a f _).mp ((kgNRSpatialKinetic a).mem_graph ⟨f,h⟩))
  · intro h
    let T : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert :=
      Multiplication.realMultiplication (kgNRFrequencyKineticEnergy a)
    have hg := T.mem_graph ⟨𝓕 f,h⟩
    have hi : (𝓕 f,𝓕 (𝓕⁻ (T ⟨𝓕 f,h⟩))) ∈ T.graph := by
      simpa only [FourierTransform.fourier_fourierInv_eq] using hg
    exact LinearPMap.mem_domain_of_mem_graph
      ((kg_nr_spatial_kinetic_fourier_graph a f _).mpr hi)

def kgSpatialWeakKineticGraph (a : Parameters) (f g : KGNRSpatialHilbert) : Prop :=
  (g : KGSpatialDistribution) =
    (-(a.hbar ^ 2 / (2 * a.mass)) : ℂ) •
      kgSpatialDistributionLaplacian (f : KGSpatialDistribution)

theorem kg_nr_frequency_symbol_temperate (a : Parameters) :
    (fun x => (kgNRFrequencyKineticEnergy a x : ℂ)).HasTemperateGrowth := by
  have h : (fun x : KGSpatialSpace =>
      ((a.hbar ^ 2 / (2 * a.mass)) : ℂ) * -kgSpatialLaplacianSymbol x).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).mul
      kg_spatial_laplacian_symbol_temperate.neg
  convert h using 1
  funext x
  rw [kg_nr_frequency_kinetic_symbol,kg_spatial_laplacian_symbol_value]
  push_cast
  ring

theorem kg_nr_spatial_kinetic_weak_graph (a : Parameters) (f g : KGNRSpatialHilbert) :
    (f,g) ∈ (kgNRSpatialKinetic a).graph ↔ kgSpatialWeakKineticGraph a f g := by
  rw [kg_nr_spatial_kinetic_fourier_graph,Multiplication.realMultiplication_mem_graph,
    ← kg_spatial_distribution_multiplier_eq_iff _ (kg_nr_frequency_symbol_temperate a)]
  have hs : (fun x => (kgNRFrequencyKineticEnergy a x : ℂ)) =
      (-(a.hbar ^ 2 / (2 * a.mass)) : ℂ) • kgSpatialLaplacianSymbol := by
    funext x
    rw [Pi.smul_apply,smul_eq_mul,kg_nr_frequency_kinetic_symbol,
      kg_spatial_laplacian_symbol_value]
    push_cast
    ring
  rw [hs,TemperedDistribution.smulLeftCLM_smul kg_spatial_laplacian_symbol_temperate]
  change ((𝓕 g : KGNRSpatialHilbert) : KGSpatialDistribution) =
    (-(a.hbar ^ 2 / (2 * a.mass)) : ℂ) •
      TemperedDistribution.smulLeftCLM ℂ kgSpatialLaplacianSymbol
        ((𝓕 f : KGNRSpatialHilbert) : KGSpatialDistribution) ↔ _
  rw [← Lp.fourier_toTemperedDistribution_eq,← Lp.fourier_toTemperedDistribution_eq,
    ← kg_spatial_distribution_laplacian_fourier,← FourierTransform.fourier_smul]
  unfold kgSpatialWeakKineticGraph
  constructor
  · intro h
    have hi := congrArg (fun T : KGSpatialDistribution => 𝓕⁻ T) h
    simpa only [FourierTransform.fourierInv_fourier_eq] using hi
  · intro h
    exact congrArg (fun T : KGSpatialDistribution => 𝓕 T) h

theorem kg_nr_spatial_kinetic_maximal_weak_domain (a : Parameters)
    (f : KGNRSpatialHilbert) :
    f ∈ (kgNRSpatialKinetic a).domain ↔
      ∃ g : KGNRSpatialHilbert, kgSpatialWeakKineticGraph a f g := by
  constructor
  · intro hf
    exact ⟨kgNRSpatialKinetic a ⟨f,hf⟩,
      (kg_nr_spatial_kinetic_weak_graph a f _).mp
        ((kgNRSpatialKinetic a).mem_graph ⟨f,hf⟩)⟩
  · rintro ⟨g,hg⟩
    exact LinearPMap.mem_domain_of_mem_graph
      ((kg_nr_spatial_kinetic_weak_graph a f g).mpr hg)

def kgNRSpatialFreeFlow (a : Parameters) (t : ℝ) :
    KGNRSpatialHilbert ≃ₗᵢ[ℂ] KGNRSpatialHilbert :=
  ((kgPhysicalSpatialUnitary a).symm.trans (kgNRFreeMomentumFlow a t)).trans
    (kgPhysicalSpatialUnitary a)

def kgOriginalRestSpatialFlow (a : Parameters) (c t : ℝ)
    (f : KGNRSpatialHilbert) : KGNRSpatialHilbert :=
  kgPhysicalSpatialUnitary a
    (kgTransportedIsolatedRestFlow a c t ((kgPhysicalSpatialUnitary a).symm f))

theorem kg_original_rest_spatial_strong_nr_limit (a : Parameters) (t : ℝ)
    (f : KGNRSpatialHilbert) :
    Tendsto (fun c : ℝ => kgOriginalRestSpatialFlow a c t f) atTop
      (nhds (kgNRSpatialFreeFlow a t f)) :=
  ((kgPhysicalSpatialUnitary a).continuous.continuousAt.tendsto).comp
    (kg_transported_isolated_rest_flow_strong_limit a t ((kgPhysicalSpatialUnitary a).symm f))

theorem kg_nr_spatial_free_flow_generator (a : Parameters)
    (f : (kgNRSpatialKinetic a).domain) :
    HasDerivAt (fun t => kgNRSpatialFreeFlow a t f.val)
      (Translation.coefficient a.hbar • kgNRSpatialKinetic a f) 0 := by
  have h := kg_nr_free_momentum_flow_generator a
    ⟨(kgPhysicalSpatialUnitary a).symm f.val,f.prop⟩
  have ht :=
    ((kgPhysicalSpatialUnitary a).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      0 h
  change HasDerivAt
    (fun t : ℝ => kgPhysicalSpatialUnitary a
      (kgNRFreeMomentumFlow a t ((kgPhysicalSpatialUnitary a).symm f.val)))
    (kgPhysicalSpatialUnitary a (Translation.coefficient a.hbar •
      kgNRFreeMomentumGenerator a ⟨(kgPhysicalSpatialUnitary a).symm f.val,f.prop⟩)) 0 at ht
  simpa only [kgNRSpatialFreeFlow, LinearIsometryEquiv.trans_apply,
    kgNRSpatialKinetic, AASCSpatial.unitaryTransport_apply, map_smul] using ht

end AASCKleinGordon
