import SKGConformalMetricCalculus
import KernelFaithfulCurvedKGCompletion

/-! The exact accepted metric, scalar Cauchy family and receiving domain.
Regularity/nondegeneracy are derived from the constructed compact operand. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

abbrev sourceMetric (a : Parameters) : MetricField :=
  originalEHActMetric (conformalOperand (conformalFrequency a))

abbrev sourceFactor (a : Parameters) : CoordinatePoint → ℝ :=
  conformalMetricFactor (conformalFrequency a)

def sourceDomain (a : Parameters) : Opens CoordinatePoint :=
  ⟨protectedDiamond (conformalFrequency a), protected_diamond_open _⟩

abbrev sourceField (a : Parameters) (f h : CurvedCauchyDatum a) : CoordinatePoint → ℝ :=
  compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h

theorem source_factor_positive (a : Parameters) (p : CoordinatePoint) :
    0 < sourceFactor a p := conformal_metric_factor_positive _ p

theorem source_factor_nonzero (a : Parameters) (p : CoordinatePoint) :
    sourceFactor a p ≠ 0 := ne_of_gt (source_factor_positive a p)

theorem source_factor_smooth (a : Parameters) : ContDiff ℝ (⊤ : ℕ∞) (sourceFactor a) :=
  contDiff_const.add (conformalProfile (conformalFrequency a)).contDiff

theorem source_metric_conformal (a : Parameters) :
    sourceMetric a = scalarConformalMetric (sourceFactor a) := same_eh_metric_is_scalar_conformal a

theorem source_metric_symmetric (a : Parameters) : MetricFieldSymmetric (sourceMetric a) := by
  rw [source_metric_conformal]
  exact scalar_conformal_symmetric _

theorem source_metric_smooth (a : Parameters) : SmoothCoordinateMetric (sourceMetric a) := by
  intro i j
  rw [source_metric_conformal]
  exact ((source_factor_smooth a).mul contDiff_const).of_le (by simp)

theorem source_metric_continuous (a : Parameters) : Continuous (sourceMetric a) := by
  rw [source_metric_conformal]
  exact (source_factor_smooth a).continuous.smul continuous_const

theorem source_metric_determinant_negative (a : Parameters) (p : CoordinatePoint) :
    (sourceMetric a p).det < 0 := by
  rw [source_metric_conformal, scalar_conformal_determinant]
  exact neg_neg_of_pos (pow_pos (source_factor_positive a p) 4)

theorem source_metric_nondegenerate (a : Parameters) (p : CoordinatePoint) :
    (sourceMetric a p).det ≠ 0 := ne_of_lt (source_metric_determinant_negative a p)

theorem source_metric_native_volume (a : Parameters) (p : CoordinatePoint) :
    nativeRealClockVolume (sourceMetric a p) = sourceFactor a p ^ 2 := by
  rw [source_metric_conformal, scalar_conformal_native_volume]

theorem source_metric_coordinate_volume (a : Parameters) (p : CoordinatePoint) :
    coordinateVolumeDensity (sourceMetric a) p = sourceFactor a p ^ 2 := by
  rw [source_metric_conformal, scalar_conformal_coordinate_volume]

theorem source_field_smooth (a : Parameters) (f h : CurvedCauchyDatum a) :
    ContDiff ℝ (⊤ : ℕ∞) (sourceField a f h) := compact_curved_field_smooth a _ f h

theorem source_field_equation (a : Parameters) (f h : CurvedCauchyDatum a)
    (p : CoordinatePoint) (inside : p ∈ sourceDomain a) :
    scalarFieldWaveOperator (sourceMetric a) (sourceField a f h) p =
      massWaveNumber a ^ 2 * sourceField a f h p :=
  compact_curved_field_equation a _ f h p (protected_diamond_subset_ball _ inside)

theorem source_domain_zero (a : Parameters) : (0 : CoordinatePoint) ∈ sourceDomain a :=
  protected_diamond_zero _

end AASCKleinGordon.SameActionSource
