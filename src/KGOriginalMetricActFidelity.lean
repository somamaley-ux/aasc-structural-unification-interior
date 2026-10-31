import KGOriginalInteriorReferences

/-! The metric-field projection is the original finite-act projection, fixed
before source representation. Its tangent is uniquely forced by the actual
curve. All first directions occur among the admitted compact C1 paths. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace AASCSemanticExhaustion

theorem kg_original_metric_act_faithful (Ω : Opens CoordinatePoint) :
    Function.Injective (wickOriginalRoleMetricProjection Ω) :=
  wick_original_role_metric_projection_injective Ω

theorem kg_original_metric_act_value (Ω : Opens CoordinatePoint) (H : WickKGAdmittedFiniteMetric Ω)
    (x : Spacetime) :
    wickOriginalRoleMetricProjection Ω H x=wickFlatMetric+wickNativeMetricVariation H.val x := rfl

theorem kg_original_metric_act_lorentzian (Ω : Opens CoordinatePoint)
    (H : WickKGAdmittedFiniteMetric Ω) (x : Spacetime) :
    WickLorentzSignature (wickOriginalRoleMetricProjection Ω H x) :=
  wick_original_metric_domain_fixed_signature Ω H.val H.property x

theorem kg_original_metric_act_nondegenerate (Ω : Opens CoordinatePoint)
    (H : WickKGAdmittedFiniteMetric Ω) (x : Spacetime) :
    (wickOriginalRoleMetricProjection Ω H x).det≠0 :=
  wick_original_metric_domain_nondegenerate Ω H.val H.property x

theorem kg_original_metric_act_tangent {Ω : Opens CoordinatePoint}
    (δ : WickKGFirstMetricAct Ω) (x : Spacetime) :
    HasDerivAt (fun t => wickKGFirstMetricCurve δ t x)
      (wickNativeMetricVariation (wickKGFirstTangent δ) x) 0 :=
  wick_original_role_projection_actual_tangent δ x

theorem kg_original_metric_act_tangent_unique {Ω : Opens CoordinatePoint}
    (δ : WickKGFirstMetricAct Ω) (h : MetricSourceProbe Ω)
    (derivative : ∀ x,HasDerivAt (fun t => wickKGFirstMetricCurve δ t x)
      (wickNativeMetricVariation h x) 0) : h=wickKGFirstTangent δ :=
  wick_original_role_projection_tangent_unique δ h derivative

theorem kg_original_admitted_path_covers_first_direction (Ω : Opens CoordinatePoint)
    (H : MetricSourceProbe Ω) :
    ∃ π : WickAdmittedC1MetricPath Ω,π.analytic.tangentTest=H :=
  wick_admitted_path_every_tangent Ω H

theorem kg_interior_path_first_response (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (x : WickMetricPathQresp a s Ω) (π : WickAdmittedC1MetricPath Ω) :
    wickIdentifiedMetricPathRecordReadout a s Ω x (.path π)=
      .metric (.first (kgInteriorFirstResponse a s Ω x π.analytic.tangentTest)) := by
  induction x using Quotient.inductionOn with
  | _ u =>
    have source := (wickOriginalRoleSource a s Ω u).attachment.same_original_source
    change (wickOriginalRoleSource a s Ω u).attachment.functional=
      originalWickNativeRealMetricResponse a s (originalWickUnitRepresentative a u.val) Ω at source
    change WickRoleReadout.metric (.first
      (wickAdmittedPathOutput a s (originalWickUnitRepresentative a u.val) π))=
      WickRoleReadout.metric (.first ((wickOriginalRoleSource a s Ω u).attachment.functional
        π.analytic.tangentTest))
    apply congrArg (fun z : ℝ => WickRoleReadout.metric (.first z))
    exact (wick_admitted_path_output_computed a s (originalWickUnitRepresentative a u.val) π).trans
      (congrArg (fun f : MetricSourceProbe Ω →L[ℝ] ℝ => f π.analytic.tangentTest) source).symm

end AASCKleinGordon
