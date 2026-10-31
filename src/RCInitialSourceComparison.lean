import RCSameDataFields
import SRCommonFlatGeometry

/-! Exact initial jets/source evaluations for the same real preparation.
Point identities are not spacetime-integrated response identities. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG AASCKleinGordon.SameActionSource
open scoped Topology
namespace AASCKleinGordon.RecoveryComparison

theorem same_data_central_values (a : Parameters) (f h : CurvedCauchyDatum a) (x : KGSpatialSpace) :
    sourceField a f h (centralLeafPoint x) = flatComparisonField a f h (centralLeafPoint x) :=
  same_data_initial_values a f h x

theorem source_factor_protected (a : Parameters) (p : CoordinatePoint) (inside : p ∈ sourceDomain a) :
    sourceFactor a p = secantScale (conformalFrequency a) (p 0)^2 := by
  have identity := congrArg (fun M : Tensor2 => M 0 0)
    (protected_metric_identity (conformalFrequency a) p (protected_diamond_subset_ball _ inside))
  rw [conformal_operand_actual_metric] at identity
  change sourceFactor a p * (-1) = secantScale (conformalFrequency a) (p 0)^2 * (-1) at identity
  linarith

theorem source_factor_central_leaf (a : Parameters) (x : KGSpatialSpace)
    (inside : x ∈ centralLeafDomain (conformalFrequency a)) : sourceFactor a (centralLeafPoint x)=1 := by
  rw [source_factor_protected a _ ((central_leaf_in_diamond_iff _ x).mpr inside),
    central_leaf_time,secant_scale_zero,one_pow]

theorem same_data_initial_all_jets (a : Parameters) (f h : CurvedCauchyDatum a) (x : KGSpatialSpace) :
    scalarPartial (sourceField a f h) (centralLeafPoint x) =
      scalarPartial (flatComparisonField a f h) (centralLeafPoint x) := by
  have regularC := source_field_smooth a f h
  have regularF := fixed_mass_flat_field_smooth a _ f h
  have trace : (fun y => sourceField a f h (spaceTimePoint 0 y)) =
      (fun y => flatComparisonField a f h (spaceTimePoint 0 y)) := funext (same_data_initial_values a f h)
  funext i
  refine Fin.cases (same_data_initial_time_jets a f h x) (fun j => ?_) i
  change scalarPartial (sourceField a f h) (spaceTimePoint 0 x) j.succ =
    scalarPartial (flatComparisonField a f h) (spaceTimePoint 0 x) j.succ
  rw [←scalar_join_spatial_partial _ regularC 0 x j,←scalar_join_spatial_partial _ regularF 0 x j,trace]

theorem same_initial_metric (a : Parameters) (x : KGSpatialSpace)
    (inside : x ∈ centralLeafDomain (conformalFrequency a)) :
    sourceMetric a (centralLeafPoint x) =
      originalEHActMetric (0 : MetricSourceProbe (⊤ : Opens CoordinatePoint)) (centralLeafPoint x) := by
  rw [source_metric_conformal]
  change sourceFactor a (centralLeafPoint x) • metric = _
  rw [source_factor_central_leaf a x inside,one_smul,
    AASCKleinGordon.CanonicalLicensing.SRIntegration.sr_zero_operand_is_same_flat_metric,
    original_eh_native_flat_value]

theorem same_data_initial_density (a : Parameters) (f h : CurvedCauchyDatum a)
    (x : KGSpatialSpace) (inside : x ∈ centralLeafDomain (conformalFrequency a)) :
    sameEHScalarDensity a (sourceField a f h) (centralLeafPoint x) =
      nativeRealClockDensity
        (originalEHActMetric (0 : MetricSourceProbe (⊤ : Opens CoordinatePoint)) (centralLeafPoint x))
        (scalarPartial (flatComparisonField a f h) (centralLeafPoint x))
        (flatComparisonField a f h (centralLeafPoint x)) (massWaveNumber a^2) := by
  change nativeRealClockDensity (sourceMetric a (centralLeafPoint x)) _ _ _ = _
  rw [same_initial_metric a x inside,same_data_initial_all_jets a f h x,
    same_data_central_values a f h x]

theorem same_data_initial_canonical_momentum (a : Parameters) (f h : CurvedCauchyDatum a)
    (x : KGSpatialSpace) (inside : x ∈ centralLeafDomain (conformalFrequency a)) :
    actualScalarCanonicalMomentum a (sourceField a f h) (centralLeafPoint x) =
      scalarCanonicalMomentum 1 (scalarPartial (flatComparisonField a f h) (centralLeafPoint x) 0) := by
  unfold actualScalarCanonicalMomentum
  rw [source_factor_central_leaf a x inside]
  rw [congrFun (same_data_initial_all_jets a f h x) 0]

theorem same_data_initial_stress (a : Parameters) (f h : CurvedCauchyDatum a)
    (x : KGSpatialSpace) (inside : x ∈ centralLeafDomain (conformalFrequency a)) :
    sameSourceStress a (sourceField a f h) (centralLeafPoint x) =
      scalarFieldStress (originalEHActMetric (0 : MetricSourceProbe (⊤ : Opens CoordinatePoint)))
        (flatComparisonField a f h) (massWaveNumber a^2) (centralLeafPoint x) := by
  have zeroMetric : originalEHActMetric (0 : MetricSourceProbe (⊤ : Opens CoordinatePoint)) =
      scalarConformalMetric (fun _ => 1) := by
    rw [zero_eh_metric_is_constant_conformal]
    funext p
    simp [timeConformalMetric,scalarConformalMetric]
  rw [sameSourceStress,source_metric_conformal,
    scalar_conformal_stress_polynomial _ _ _ _ (source_factor_nonzero a _),zeroMetric,
    scalar_conformal_stress_polynomial (fun _ => 1) _ _ _ one_ne_zero]
  ext i j
  change scalarPartial (sourceField a f h) (centralLeafPoint x) i *
      scalarPartial (sourceField a f h) (centralLeafPoint x) j - (1/2:ℝ)*metric i j*
      (scalarFlatKinetic (scalarPartial (sourceField a f h) (centralLeafPoint x))+
        massWaveNumber a^2*sourceFactor a (centralLeafPoint x)*sourceField a f h (centralLeafPoint x)^2) = _
  rw [same_data_initial_all_jets a f h x,same_data_central_values a f h x,source_factor_central_leaf a x inside]
  rfl

end AASCKleinGordon.RecoveryComparison
