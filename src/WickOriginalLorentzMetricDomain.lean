import WickOriginalMetricNeighborhood
import WickLorentzSchurSignature
import Mathlib.LinearAlgebra.Matrix.Gershgorin

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators Topology Matrix.Norms.Operator
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem wick_flat_spatial_block : wickSpatialBlock wickFlatMetric=1 := by
  ext i j
  simp [wickSpatialBlock,wickFlatMetric,nativeClockNormalMetric,Matrix.diagonal_apply,
    Matrix.one_apply,Fin.succ_inj]

theorem wick_original_metric_domain_negative (Ω : TopologicalSpace.Opens CoordinatePoint)
    (H : MetricSourceProbe Ω) (inside : H∈wickOriginalMetricNeighborhood Ω) (x : Spacetime) :
    wickOriginalFiniteMetric H x 0 0<0 := by
  have bound := wick_original_metric_neighborhood_coefficients Ω H inside x 0 0
  change wickFlatMetric 0 0+wickNativeMetricVariation H x 0 0<0
  norm_num [wickFlatMetric,nativeClockNormalMetric]
  linarith [(abs_lt.mp bound).2]

theorem wick_original_metric_domain_spatial_positive (Ω : TopologicalSpace.Opens CoordinatePoint)
    (H : MetricSourceProbe Ω) (inside : H∈wickOriginalMetricNeighborhood Ω) (x : Spacetime)
    (v : Fin 3 → ℝ) (hv : v≠0) :
    0<wickMatrixQuadratic (wickSpatialBlock (wickOriginalFiniteMetric H x)) v := by
  have small : ∀ i j, |wickSpatialBlock (wickNativeMetricVariation H x) i j|≤(1:ℝ)/16 :=
    fun i j => (wick_original_metric_neighborhood_coefficients Ω H inside x i.succ j.succ).le
  have split : wickSpatialBlock (wickOriginalFiniteMetric H x)=
      1+wickSpatialBlock (wickNativeMetricVariation H x) := by
    change wickSpatialBlock (wickFlatMetric+wickNativeMetricVariation H x)=_
    rw [← wick_flat_spatial_block]
    rfl
  rw [split]
  exact wick_small_spatial_block_pos _ small v hv

theorem wick_original_metric_domain_fixed_signature (Ω : TopologicalSpace.Opens CoordinatePoint)
    (H : MetricSourceProbe Ω) (inside : H∈wickOriginalMetricNeighborhood Ω) (x : Spacetime) :
    WickLorentzSignature (wickOriginalFiniteMetric H x) :=
  wick_negative_positive_split_is_lorentz _ (wick_original_finite_metric_symmetric H x)
    (wick_original_metric_domain_negative Ω H inside x)
    (wick_original_metric_domain_spatial_positive Ω H inside x)

theorem wick_original_metric_domain_nondegenerate (Ω : TopologicalSpace.Opens CoordinatePoint)
    (H : MetricSourceProbe Ω) (inside : H∈wickOriginalMetricNeighborhood Ω) (x : Spacetime) :
    (wickOriginalFiniteMetric H x).det≠0 := by
  apply det_ne_zero_of_sum_row_lt_diag
  intro i
  have coefficients := wick_original_metric_neighborhood_coefficients Ω H inside x
  have diagonal : 15/16 < |wickOriginalFiniteMetric H x i i| := by
    have bound := coefficients i i
    have signnorm : |wickFlatMetric i i|=1 := by
      fin_cases i <;> norm_num [wickFlatMetric,nativeClockNormalMetric,Matrix.diagonal_apply] <;>
        (try simp only [Fin.ext_iff]) <;> norm_num
    have triangle := abs_add_le (wickFlatMetric i i+wickNativeMetricVariation H x i i)
      (-wickNativeMetricVariation H x i i)
    rw [add_neg_cancel_right,abs_neg,signnorm] at triangle
    change 15/16 < |wickFlatMetric i i+wickNativeMetricVariation H x i i|
    linarith
  have off : ∀ j∈Finset.univ.erase i,
      ‖wickOriginalFiniteMetric H x i j‖≤(1:ℝ)/16 := by
    intro j hj
    have ne : i≠j := Ne.symm (Finset.ne_of_mem_erase hj)
    have flat : wickFlatMetric i j=0 := by
      simp [wickFlatMetric,nativeClockNormalMetric,Matrix.diagonal_apply,ne]
    change |wickFlatMetric i j+wickNativeMetricVariation H x i j|≤(1:ℝ)/16
    rw [flat,zero_add]
    exact (coefficients i j).le
  have total := Finset.sum_le_sum off
  have cardinal : (Finset.univ.erase i).card=3 := by simp
  simp only [Finset.sum_const,cardinal,nsmul_eq_mul] at total
  change (∑ j∈Finset.univ.erase i,‖wickOriginalFiniteMetric H x i j‖)<
    |wickOriginalFiniteMetric H x i i|
  linarith

end AASCKleinGordon
