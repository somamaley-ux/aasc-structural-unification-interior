import RCObservationBounds

/-! The limiting numeric overlap is an actual retained original comparison
readout. Convergence concerns its numeric value, not arbitrary Option records. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 240000
open MeasureTheory Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.RecoveryComparison
open KGQuantum W9
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace
attribute [local irreducible] kgOriginalSpatialCoreEquiv kgPhysicalSpatialUnitary kgNRSpatialCoreFlow

def originalCoreComparisonValue (a : Parameters) (t : ℝ)
    (x z : PureVector (kgOriginalSpatialCore a)) : ℝ :=
  transitionProbability z (PureVector.mapUnitary (kgNRSpatialCoreFlow a t) x)

theorem original_core_comparison_readout (a : Parameters) (s t : ℝ) (Ω : Opens CoordinatePoint)
    (x z : PureVector (kgOriginalSpatialCore a)) :
    kgSpatialSourceRecord a s Ω (rayMap _ (PureVector.mapUnitary (kgNRSpatialCoreFlow a t) x))
      (.reverseComparison (kgPureIsometryMap (K := fockCoreDomain a) (kgSpatialCoreOriginalEmbedding a) z)) =
        .comparison (originalCoreComparisonValue a t x z) := by
  rw [kg_spatial_source_complete_record]
  change KGFamilyReadout.comparison (transitionProbability
    (kgPureIsometryMap (K := fockCoreDomain a) (kgSpatialCoreOriginalEmbedding a) z)
    (kgPureIsometryMap (K := fockCoreDomain a) (kgSpatialCoreOriginalEmbedding a) (PureVector.mapUnitary (kgNRSpatialCoreFlow a t) x))) = _
  rw [kg_pure_isometry_weight]
  rfl

theorem original_core_comparison_is_normalized_overlap (a : Parameters) (t : ℝ)
    (x z : PureVector (kgOriginalSpatialCore a)) (hx : ‖x.val‖=1) (hz : ‖z.val‖=1) :
    originalCoreComparisonValue a t x z = ‖inner ℂ z.val.val (kgNRSpatialFreeFlow a t x.val.val)‖^2 := by
  have normFlow : ‖kgNRSpatialCoreFlow a t x.val‖=1 := (kgNRSpatialCoreFlow a t).norm_map x.val |>.trans hx
  unfold originalCoreComparisonValue transitionProbability
  simp only [PureVector.coe_mapUnitary,hz,normFlow,one_pow,one_mul,div_one]
  change ‖inner ℂ z.val.val (kgNRSpatialCoreFlow a t x.val).val‖^2 = _
  rw [kg_nr_spatial_core_flow_full_value]

theorem original_numeric_comparison_compact_time (a : Parameters)
    (x z : PureVector (kgOriginalSpatialCore a)) (hx : ‖x.val‖=1) (hz : ‖z.val‖=1)
    (T : ℝ) (hT : 0 ≤ T) (epsilon : ℝ) (positive : 0 < epsilon) :
    ∀ᶠ c : ℝ in atTop, ∀ t : ℝ, |t| ≤ T →
      |‖inner ℂ z.val.val (kgOriginalRestSpatialFlow a c t x.val.val)‖^2-
        originalCoreComparisonValue a t x z| < epsilon := by
  filter_upwards [spatial_probability_compact_time a x.val.val z.val.val hx hz T hT epsilon positive] with c hc
  intro t ht
  rw [original_core_comparison_is_normalized_overlap a t x z hx hz]
  exact hc t ht

end AASCKleinGordon.RecoveryComparison
