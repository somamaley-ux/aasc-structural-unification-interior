import WickNativeNormalizedSourceAssembly

noncomputable section
open TopologicalSpace
open scoped Matrix.Norms.Operator
open AASCSemanticExhaustion
namespace AASCKleinGordon

/-- The metric projection of the original admitted finite-action carrier.
It is fixed before any source witness or tensor representation. -/
def wickOriginalRoleMetricProjection (Ω : Opens CoordinatePoint) :
    WickKGAdmittedFiniteMetric Ω → (Spacetime → NativeRealMatrix) :=
  fun H => wickOriginalFiniteMetric H.val

theorem wick_original_role_metric_projection_injective (Ω : Opens CoordinatePoint) :
    Function.Injective (wickOriginalRoleMetricProjection Ω) := by
  intro H K same
  apply Subtype.ext
  apply DFunLike.ext
  intro p
  have encoded : tensorEncode (H.val p)=tensorEncode (K.val p) := by
    funext i j
    have entry := congrArg (fun f => f (wickSpacetimeCoordinates.symm p) i j) same
    change wickFlatMetric i j + tensorEncode (H.val p) i j =
      wickFlatMetric i j + tensorEncode (K.val p) i j at entry
    exact add_left_cancel entry
  simpa only [tensor_decode_encode] using congrArg tensorDecode encoded

theorem wick_original_role_projection_actual_tangent {Ω : Opens CoordinatePoint}
    (δ : WickKGFirstMetricAct Ω) (x : Spacetime) :
    HasDerivAt (fun t => wickKGFirstMetricCurve δ t x)
      (wickNativeMetricVariation (wickKGFirstTangent δ) x) 0 :=
  wick_KG_original_act_tangent δ x

theorem wick_original_role_projection_tangent_unique {Ω : Opens CoordinatePoint}
    (δ : WickKGFirstMetricAct Ω) (h : MetricSourceProbe Ω)
    (derivative : ∀ x,HasDerivAt (fun t => wickKGFirstMetricCurve δ t x)
      (wickNativeMetricVariation h x) 0) : h=wickKGFirstTangent δ := by
  apply DFunLike.ext
  intro p
  have same := (derivative (wickSpacetimeCoordinates.symm p)).unique
    (wick_KG_original_act_tangent δ (wickSpacetimeCoordinates.symm p))
  change tensorEncode (h p)=tensorEncode (wickKGFirstTangent δ p) at same
  simpa only [tensor_decode_encode] using congrArg tensorDecode same

end AASCKleinGordon
