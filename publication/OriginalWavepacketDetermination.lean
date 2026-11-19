import KGNRSourceCoreFlow
import KGNRReceivingCertificate
import KGNRFreeExactGenerator

/-!
# Determination by original wavepacket amplitudes

The tests in this module use the transported original one-particle core and the
finite-speed rest-subtracted dynamics. Both arguments of an amplitude are
phase-fixed vectors. The test does not identify a complex amplitude with a ray
transition probability.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

open AASCKleinGordon Filter MeasureTheory

namespace AASCOriginalWavepacket

/-- The image of the actual original one-particle core is dense in the
completed spatial Hilbert space. -/
theorem original_core_dense (a : Parameters) :
    DenseRange (kgOriginalOneCoreSpatialEmbedding a) := by
  have normalized := (kgWeightedMomentumUnitary a).surjective.denseRange.comp
    (oneParticleSchwartz_dense a) (kgWeightedMomentumUnitary a).continuous
  have transported := (kgPhysicalSpatialUnitary a).surjective.denseRange.comp
    normalized (kgPhysicalSpatialUnitary a).continuous
  apply transported.mono
  rintro _ ⟨f, rfl⟩
  refine ⟨kgOriginalOneCoreOfSchwartz a f, ?_⟩
  rw [kg_original_one_core_spatial_formula, kg_original_one_core_momentum_coordinates,
    kg_original_one_core_coordinates_of_schwartz]
  rfl

/-- Agreement with the actual finite-speed original dynamics is tested by
complex matrix elements at rational times. Its inputs are original
preparations and probes; no candidate spatial differential expression occurs. -/
def OriginalAmplitudeLimits (a : Parameters)
    (U : ℝ → KGNRSpatialHilbert → KGNRSpatialHilbert) : Prop :=
  ∀ (q : ℚ) (f g : kgOriginalOneCore a),
    let embed := kgOriginalOneCoreSpatialEmbedding a
    Tendsto
      (fun c : ℝ => inner ℂ (embed g) (kgOriginalRestSpatialFlow a c (q : ℝ) (embed f)))
      atTop (nhds (inner ℂ (embed g) (U (q : ℝ) (embed f))))

/-- The constructed free flow realizes every test. -/
theorem free_flow_has_original_wavepacket_limits (a : Parameters) :
    OriginalAmplitudeLimits a (fun t f => kgNRSpatialFreeFlow a t f) := by
  intro q f g
  exact ((innerSL ℂ (kgOriginalOneCoreSpatialEmbedding a g)).continuous.tendsto _).comp
    (kg_original_rest_spatial_strong_nr_limit a (q : ℝ) (kgOriginalOneCoreSpatialEmbedding a f))

/-- Every separately continuous candidate with these original amplitudes is
the full free flow. No group, linearity, locality or finite-order hypothesis
is needed on the candidate. -/
theorem flow_of_original_wavepacket_limits (a : Parameters)
    (U : ℝ → KGNRSpatialHilbert → KGNRSpatialHilbert)
    (stateContinuous : ∀ t, Continuous (U t))
    (timeContinuous : ∀ f, Continuous (fun t => U t f))
    (observed : OriginalAmplitudeLimits a U) :
    ∀ t f, U t f = kgNRSpatialFreeFlow a t f := by
  let embed := kgOriginalOneCoreSpatialEmbedding a
  have dense : DenseRange embed := original_core_dense a
  have rational (q : ℚ) : U (q : ℝ) = fun f => kgNRSpatialFreeFlow a (q : ℝ) f := by
    apply (stateContinuous _).ext_on dense (kgNRSpatialFreeFlow a (q : ℝ)).continuous
    rintro _ ⟨f, rfl⟩
    apply ext_inner_left ℂ
    intro h
    have probes : (fun g => inner ℂ g (U (q : ℝ) (embed f))) =
        (fun g => inner ℂ g (kgNRSpatialFreeFlow a (q : ℝ) (embed f))) := by
      apply (continuous_id.inner continuous_const).ext_on dense
        (continuous_id.inner continuous_const)
      rintro _ ⟨g, rfl⟩
      exact tendsto_nhds_unique (observed q f g)
        (((innerSL ℂ (embed g)).continuous.tendsto _).comp
          (kg_original_rest_spatial_strong_nr_limit a (q : ℝ) (embed f)))
    exact congrFun probes h
  intro t f
  have times : (fun s => U s f) = (fun s => kgNRSpatialFreeFlow a s f) := by
    apply (timeContinuous f).ext_on Rat.denseRange_cast (kg_nr_full_spatial_time_continuous a f)
    rintro _ ⟨q, rfl⟩
    exact congrFun (rational q) f
  exact congrFun times t

/-- An exact generator for a separately time-continuous candidate unitary
family passing the original amplitude tests has the kinetic operator's full
domain and values, by equality of partially defined linear operators. -/
theorem generator_of_original_wavepacket_limits (a : Parameters)
    (U : ℝ → KGNRSpatialHilbert ≃ₗᵢ[ℂ] KGNRSpatialHilbert)
    (timeContinuous : ∀ f, Continuous (fun t => U t f))
    (observed : OriginalAmplitudeLimits a (fun t f => U t f))
    (H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert)
    (generator : GlobalCharge.ExactGenerator (Translation.coefficient a.hbar) U H) :
    H = kgNRSpatialKinetic a := by
  have flow := flow_of_original_wavepacket_limits a (fun t f => U t f)
    (fun t => (U t).continuous) timeContinuous observed
  have same : U = kgNRSpatialFreeFlow a := by
    funext t
    apply LinearIsometryEquiv.ext
    intro f
    exact flow t f
  rw [same] at generator
  exact kg_nr_same_flow_exact_generator_unique a H generator

#print axioms original_core_dense
#print axioms free_flow_has_original_wavepacket_limits
#print axioms flow_of_original_wavepacket_limits
#print axioms generator_of_original_wavepacket_limits

end AASCOriginalWavepacket
