import OriginalEHSmallRayDomain
import WickOriginalMetricNeighborhood
import WickNativeLieAttachment

/-! The actual finite metric operand already carried by the original prepared
use. Its Lorentz frame and EH analytic admission are derived from the existing
act bound, not supplied as an EH interpretation agreement. This is the declared
original compact-neighborhood branch, not the whole gravity standing domain. -/
namespace AASCKleinGordon
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCSemanticExhaustion TopologicalSpace MeasureTheory
open scoped Topology ContDiff

variable {Ω : Opens CoordinatePoint}

def originalEHActMetric (H : MetricSourceProbe Ω) : MetricField :=
  originalEHMetricPerturbation wickNativeFlatMetric H

theorem original_eh_native_flat_value (p : CoordinatePoint) :
    wickNativeFlatMetric p = metric := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem original_eh_act_metric_same_field (H : MetricSourceProbe Ω) (x : Spacetime) :
    originalEHActMetric H (wickSpacetimeCoordinates x) = wickOriginalFiniteMetric H x := rfl

theorem original_eh_act_metric_symmetric (H : MetricSourceProbe Ω) :
    MetricFieldSymmetric (originalEHActMetric H) := by
  intro p i j
  change wickNativeFlatMetric p i j + tensorEncode (H p) i j =
    wickNativeFlatMetric p j i + tensorEncode (H p) j i
  rw [wick_native_flat_symmetric p i j,tensorEncode_symmetric]

theorem original_eh_act_metric_smooth (H : MetricSourceProbe Ω) :
    ∀ i j, ContDiff ℝ ∞ (fun p => originalEHActMetric H p i j) := by
  intro i j
  exact contDiff_const.add (eh_probe_metric_smooth H i j)

theorem original_eh_act_coefficient_bound (H : MetricSourceProbe Ω)
    (inside : H ∈ wickOriginalMetricNeighborhood Ω) (p : CoordinatePoint) (i j : Fin 4) :
    |tensorEncode (H p) i j| < (1:ℝ)/16 := by
  have bound := BoundedContinuousFunction.norm_coe_le_norm
    (wickNativeBoundedEntry Ω i j H) p
  have strict := bound.trans_lt (inside i j)
  simpa only [wick_native_bounded_entry_apply,Real.norm_eq_abs] using strict

theorem original_eh_act_metric_frame (H : MetricSourceProbe Ω)
    (inside : H ∈ wickOriginalMetricNeighborhood Ω) (p : CoordinatePoint) :
    ∃ B : CoordinatePoint ≃L[ℝ] CoordinatePoint,
      LorentzFrameAt (originalEHActMetric H) p B := by
  apply eh_symmetric_lorentz_neighborhood_has_frame
  · exact original_eh_act_metric_symmetric H p
  · apply Set.mem_iUnion.mpr
    refine ⟨ContinuousLinearEquiv.refl ℝ CoordinatePoint,?_⟩
    intro i j
    rw [coordinateFrameMatrix_refl,Matrix.transpose_one,one_mul,mul_one]
    change |wickNativeFlatMetric p i j + tensorEncode (H p) i j - metric i j| < (1:ℝ)/16
    rw [original_eh_native_flat_value]
    simpa only [add_sub_cancel_left] using original_eh_act_coefficient_bound H inside p i j

theorem original_eh_act_metric_lorentz (H : MetricSourceProbe Ω)
    (inside : H ∈ wickOriginalMetricNeighborhood Ω) (p : CoordinatePoint) :
    C2LorentzMetricAt (originalEHActMetric H) p := by
  refine ⟨original_eh_act_metric_symmetric H,?_,original_eh_act_metric_frame H inside p⟩
  intro i j
  exact (original_eh_act_metric_smooth H i j).contDiffAt.of_le
    (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

theorem original_eh_act_metric_negative (H : MetricSourceProbe Ω)
    (inside : H ∈ wickOriginalMetricNeighborhood Ω) (p : CoordinatePoint) :
    (originalEHActMetric H p).det < 0 := by
  obtain ⟨B,frame⟩ := original_eh_act_metric_frame H inside p
  exact native_lorentz_frame_determinant_negative _ p B frame

theorem original_eh_native_flat_lorentz (p : CoordinatePoint) :
    C2LorentzMetricAt wickNativeFlatMetric p := by
  refine ⟨wick_native_flat_symmetric,fun _ _ => contDiff_const.contDiffAt, 
    ContinuousLinearEquiv.refl ℝ CoordinatePoint,?_⟩
  change (coordinateFrameMatrix (ContinuousLinearEquiv.refl ℝ CoordinatePoint)).transpose *
    wickNativeFlatMetric p * coordinateFrameMatrix (ContinuousLinearEquiv.refl ℝ CoordinatePoint) = metric
  rw [coordinateFrameMatrix_refl,Matrix.transpose_one,one_mul,mul_one,original_eh_native_flat_value]

theorem original_eh_native_flat_negative (p : CoordinatePoint) :
    (wickNativeFlatMetric p).det < 0 := by
  rw [original_eh_native_flat_value,canonical_lorentz_metric_det]
  norm_num

theorem original_eh_original_act_admitted (κ Λ : ℝ) (coupling : κ ≠ 0)
    (H : MetricSourceProbe Ω) (inside : H ∈ wickOriginalMetricNeighborhood Ω) :
    OriginalEHFiniteUseDomain κ Λ wickNativeFlatMetric H := by
  refine ⟨coupling,fun p _ => original_eh_native_flat_lorentz p,
    fun p _ => original_eh_act_metric_lorentz H inside p,?_⟩
  have integrable := eh_original_admitted_relative_integrable κ Λ wickNativeFlatMetric
    wick_native_flat_symmetric (fun _ _ => contDiff_const)
    (fun p _ => original_eh_native_flat_negative p) H 1
    (by simpa only [one_smul] using
      (fun p (_ : p ∈ Ω) => original_eh_act_metric_lorentz H inside p))
  simpa only [one_smul] using integrable

theorem original_eh_original_act_evaluation (κ Λ : ℝ) (coupling : κ ≠ 0)
    (H : MetricSourceProbe Ω) (inside : H ∈ wickOriginalMetricNeighborhood Ω) :
    (originalEHFiniteUse κ Λ wickNativeFlatMetric H).2 =
      some (originalEHRelativeAction κ Λ wickNativeFlatMetric H) :=
  (original_eh_finite_use_success_exact κ Λ wickNativeFlatMetric H _).mpr
    ⟨original_eh_original_act_admitted κ Λ coupling H inside,rfl⟩

end
end AASCKleinGordon
