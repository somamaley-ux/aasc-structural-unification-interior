import WickLorentzSignatureDomain

/-! LF-open finite-deformation neighborhood of the original scalar action.
All native compact directions enter this neighborhood for sufficiently small
parameter. There is no globally fixed support or response equation in its data. -/
noncomputable section
set_option maxHeartbeats 1000000
open Set TopologicalSpace Filter
open scoped Topology Matrix.Norms.Operator
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickNativeRealEntryCLM (i j : Fin 4) : (Fin 10 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp
    ((ContinuousLinearMap.proj i).comp tensorEncodeLinear.toContinuousLinearMap)

def wickNativeBoundedEntry (Ω : Opens CoordinatePoint) (i j : Fin 4) :
    MetricSourceProbe Ω →L[ℝ] BoundedContinuousFunction CoordinatePoint ℝ :=
  (TestFunction.toBoundedContinuousFunctionCLM ℝ).comp
    (TestFunction.postcompCLM (wickNativeRealEntryCLM i j))

theorem wick_native_bounded_entry_apply (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω)
    (i j : Fin 4) (x : CoordinatePoint) :
    wickNativeBoundedEntry Ω i j H x=tensorEncode (H x) i j := rfl

def wickOriginalMetricNeighborhood (Ω : Opens CoordinatePoint) : Set (MetricSourceProbe Ω) :=
  {H | ∀ i j, ‖wickNativeBoundedEntry Ω i j H‖ < (1:ℝ)/16}

theorem wick_original_metric_neighborhood_open (Ω : Opens CoordinatePoint) :
    IsOpen (wickOriginalMetricNeighborhood Ω) := by
  unfold wickOriginalMetricNeighborhood
  simpa only [Set.setOf_forall] using isOpen_iInter_of_finite (fun i : Fin 4 => isOpen_iInter_of_finite (fun j : Fin 4 =>
    isOpen_lt (continuous_norm.comp (wickNativeBoundedEntry Ω i j).continuous) continuous_const))

theorem wick_original_metric_neighborhood_zero (Ω : Opens CoordinatePoint) :
    (0 : MetricSourceProbe Ω)∈wickOriginalMetricNeighborhood Ω := by
  intro i j
  simp

theorem wick_original_metric_neighborhood_all_directions (Ω : Opens CoordinatePoint)
    (H : MetricSourceProbe Ω) :
    ∀ᶠ t : ℝ in 𝓝 0,t • H∈wickOriginalMetricNeighborhood Ω := by
  have hc : Continuous (fun t : ℝ => t • H) := continuous_id.smul continuous_const
  have hzero : (fun t : ℝ => t • H) 0∈wickOriginalMetricNeighborhood Ω := by
    simpa using wick_original_metric_neighborhood_zero Ω
  exact hc.continuousAt ((wick_original_metric_neighborhood_open Ω).mem_nhds hzero)

theorem wick_original_metric_neighborhood_coefficients (Ω : Opens CoordinatePoint)
    (H : MetricSourceProbe Ω) (inside : H∈wickOriginalMetricNeighborhood Ω)
    (x : Spacetime) (i j : Fin 4) :
    |wickNativeMetricVariation H x i j| < (1:ℝ)/16 := by
  exact (BoundedContinuousFunction.norm_coe_le_norm
    (wickNativeBoundedEntry Ω i j H) (wickSpacetimeCoordinates x)).trans_lt (inside i j)

def wickOriginalFiniteMetric {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) :
    Spacetime → NativeRealMatrix := fun x => wickFlatMetric+wickNativeMetricVariation H x

theorem wick_original_finite_metric_smooth {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) :
    ContDiff ℝ (⊤ : ℕ∞) (wickOriginalFiniteMetric H) :=
  contDiff_const.add (wick_native_metric_variation_smooth H)

theorem wick_original_finite_metric_symmetric {Ω : Opens CoordinatePoint}
    (H : MetricSourceProbe Ω) (x : Spacetime) (i j : Fin 4) :
    wickOriginalFiniteMetric H x i j=wickOriginalFiniteMetric H x j i := by
  change wickFlatMetric i j+wickNativeMetricVariation H x i j=
    wickFlatMetric j i+wickNativeMetricVariation H x j i
  rw [wick_native_metric_variation_symmetric H x i j]
  congr 1
  fin_cases i <;> fin_cases j <;> rfl

theorem wick_original_finite_metric_off_support {Ω : Opens CoordinatePoint}
    (H : MetricSourceProbe Ω) (x : Spacetime) (outside : x∉tsupport (wickNativeMetricVariation H)) :
    wickOriginalFiniteMetric H x=wickFlatMetric := by
  simp only [wickOriginalFiniteMetric,image_eq_zero_of_notMem_tsupport outside,add_zero]

end AASCKleinGordon
