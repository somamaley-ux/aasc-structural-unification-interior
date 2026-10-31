import KGMetricActCharts

/-! Actual metric-field redescription between arbitrary labelled receiving
frames. The intermediate inverse congruence recovers the same anchored field;
the subsequent congruence presents it in the destination frame. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open TopologicalSpace AASCSemanticExhaustion

theorem kg_metric_act_admission_identity (Ω : Opens CoordinatePoint) :
    wickMetricProbeRegionCongr (wick_affine_region_one Ω) ''
      wickTransportedMetricDomain 0 1 Ω=wickOriginalMetricNeighborhood Ω := by
  unfold wickTransportedMetricDomain
  rw [Set.image_image]
  have same : (fun H : MetricSourceProbe Ω =>
      wickMetricProbeRegionCongr (wick_affine_region_one Ω)
        (wickNativeAffineMetricTest 0 1 H))=id :=
    funext (wick_native_affine_test_one Ω)
  change (fun H : MetricSourceProbe Ω =>
    wickMetricProbeRegionCongr (wick_affine_region_one Ω)
      (wickNativeAffineMetricTest 0 1 H)) '' wickOriginalMetricNeighborhood Ω=_
  rw [same,Set.image_id]

theorem kg_metric_act_admission_composition (b c : Spacetime)
    (L M : ProperLorentzTransform) (Ω : Opens CoordinatePoint) :
    wickMetricProbeRegionCongr (wick_affine_region_comp b c L M Ω) ''
      (wickNativeAffineMetricTest b L '' wickTransportedMetricDomain c M Ω)=
      wickTransportedMetricDomain (b+spacetimeLorentzCLE L c) (L*M) Ω := by
  unfold wickTransportedMetricDomain
  rw [Set.image_image,Set.image_image]
  congr 1
  funext H
  exact wick_native_affine_test_comp b c L M Ω H

theorem kg_metric_act_inverse_congruence (L : ProperLorentzTransform)
    (G : NativeRealMatrix) :
    (wickLorentzMatrix L).transpose*
      ((wickLorentzMatrix L⁻¹).transpose*G*wickLorentzMatrix L⁻¹)*
      wickLorentzMatrix L=G := by
  have inverse : wickLorentzMatrix L⁻¹*wickLorentzMatrix L=1 := by
    rw [← wick_lorentz_matrix_mul,inv_mul_cancel,wick_lorentz_matrix_one]
  calc
    _=(wickLorentzMatrix L⁻¹*wickLorentzMatrix L).transpose*G*
        (wickLorentzMatrix L⁻¹*wickLorentzMatrix L) := by
      simp only [Matrix.transpose_mul,Matrix.mul_assoc]
    _=G := by rw [inverse]; simp only [Matrix.transpose_one,Matrix.one_mul,Matrix.mul_one]

theorem kg_metric_act_chart_field_transition (p q : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (H : KGMetricActChart p Ω) (x : Spacetime) :
    kgMetricActChartProjection q Ω (kgMetricActChartChange p q Ω H)
        (q.left.toAdd+spacetimeLorentzCLE q.right x)=
      (wickLorentzMatrix q.right⁻¹).transpose*
        ((wickLorentzMatrix p.right).transpose*
          kgMetricActChartProjection p Ω H
            (p.left.toAdd+spacetimeLorentzCLE p.right x)*
          wickLorentzMatrix p.right)*wickLorentzMatrix q.right⁻¹ := by
  let K := (kgMetricActChartEquiv p Ω).symm H
  have recover : kgMetricActChartEquiv p Ω K=H :=
    (kgMetricActChartEquiv p Ω).apply_symm_apply H
  rw [← recover,kg_metric_act_chart_change_original,
    kg_metric_act_chart_field_covariance,kg_metric_act_chart_field_covariance,
    kg_metric_act_inverse_congruence]

end AASCKleinGordon
