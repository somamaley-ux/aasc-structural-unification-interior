import KGPairedInteriorFidelity

/-! Actual finite metric acts in receiving frames. The carrier is the admitted
compact metric test, and its projection is the actual field g0+H. Frame changes
move the admission set. They confer no authority on source or quantum standing. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open TopologicalSpace AASCSemanticExhaustion

def KGMetricActChart (q : ProperPoincareTransform) (Ω : Opens CoordinatePoint) :=
  {H : MetricSourceProbe (wickAffineMetricRegion q.left.toAdd q.right Ω) //
    H ∈ wickTransportedMetricDomain q.left.toAdd q.right Ω}

def kgMetricActChartEquiv (q : ProperPoincareTransform) (Ω : Opens CoordinatePoint) :
    WickKGAdmittedFiniteMetric Ω ≃ KGMetricActChart q Ω where
  toFun H := ⟨wickNativeAffineMetricTest q.left.toAdd q.right H.val,
    ⟨H.val,H.property,rfl⟩⟩
  invFun J := ⟨wickNativeAffineMetricInverseCLM q.left.toAdd q.right Ω J.val, by
    obtain ⟨H,inside,same⟩ := J.property
    rw [← same,wick_native_affine_inverse_left]
    exact inside⟩
  left_inv H := Subtype.ext (wick_native_affine_inverse_left _ _ _ H.val)
  right_inv J := Subtype.ext (wick_native_affine_inverse_right _ _ _ J.val)

def kgMetricActChartChange (p q : ProperPoincareTransform) (Ω : Opens CoordinatePoint) :
    KGMetricActChart p Ω ≃ KGMetricActChart q Ω :=
  (kgMetricActChartEquiv p Ω).symm.trans (kgMetricActChartEquiv q Ω)

theorem kg_metric_act_chart_change_value (p q : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (H : KGMetricActChart p Ω) :
    (kgMetricActChartChange p q Ω H).val =
      wickNativeAffineMetricTest q.left.toAdd q.right
        (wickNativeAffineMetricInverseCLM p.left.toAdd p.right Ω H.val) := rfl

theorem kg_metric_act_chart_change_identity (p : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (H : KGMetricActChart p Ω) :
    kgMetricActChartChange p p Ω H=H :=
  (kgMetricActChartEquiv p Ω).apply_symm_apply H

theorem kg_metric_act_chart_change_composition (p q r : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (H : KGMetricActChart p Ω) :
    kgMetricActChartChange q r Ω (kgMetricActChartChange p q Ω H)=
      kgMetricActChartChange p r Ω H := by
  change (kgMetricActChartEquiv r Ω)
    ((kgMetricActChartEquiv q Ω).symm ((kgMetricActChartEquiv q Ω)
      ((kgMetricActChartEquiv p Ω).symm H)))=_
  rw [Equiv.symm_apply_apply]
  rfl

theorem kg_metric_act_chart_change_original (p q : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (H : WickKGAdmittedFiniteMetric Ω) :
    kgMetricActChartChange p q Ω (kgMetricActChartEquiv p Ω H)=
      kgMetricActChartEquiv q Ω H := by
  change (kgMetricActChartEquiv q Ω)
    ((kgMetricActChartEquiv p Ω).symm ((kgMetricActChartEquiv p Ω) H))=_
  rw [Equiv.symm_apply_apply]

def kgMetricActChartProjection (q : ProperPoincareTransform) (Ω : Opens CoordinatePoint) :
    KGMetricActChart q Ω → (Spacetime → NativeRealMatrix) :=
  fun H => wickOriginalFiniteMetric H.val

theorem kg_metric_act_chart_projection_injective (q : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) : Function.Injective (kgMetricActChartProjection q Ω) := by
  intro H K same
  apply Subtype.ext
  apply TestFunction.ext
  intro p
  have encoded : tensorEncode (H.val p)=tensorEncode (K.val p) := by
    funext i j
    have entry := congrArg (fun f => f (wickSpacetimeCoordinates.symm p) i j) same
    change wickFlatMetric i j+tensorEncode (H.val p) i j =
      wickFlatMetric i j+tensorEncode (K.val p) i j at entry
    exact add_left_cancel entry
  simpa only [tensor_decode_encode] using congrArg tensorDecode encoded

theorem kg_metric_act_chart_field_covariance (q : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (H : WickKGAdmittedFiniteMetric Ω) (x : Spacetime) :
    kgMetricActChartProjection q Ω (kgMetricActChartEquiv q Ω H)
        (q.left.toAdd+spacetimeLorentzCLE q.right x)=
      (wickLorentzMatrix q.right⁻¹).transpose*
        wickOriginalRoleMetricProjection Ω H x*wickLorentzMatrix q.right⁻¹ :=
  wick_native_affine_finite_metric q.left.toAdd q.right H.val x

theorem kg_metric_act_chart_signature (q : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (H : KGMetricActChart q Ω) (x : Spacetime) :
    WickIntrinsicLorentzSignature (kgMetricActChartProjection q Ω H x) ∧
      (kgMetricActChartProjection q Ω H x).det≠0 :=
  wick_transported_metric_signature q.left.toAdd q.right Ω H.val H.property x

theorem kg_metric_act_chart_anchor (q : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (x : Spacetime) :
    kgMetricActChartProjection q Ω
      (kgMetricActChartEquiv q Ω ⟨0,wick_original_metric_neighborhood_zero Ω⟩) x=
      wickFlatMetric := by
  change wickOriginalFiniteMetric (wickNativeAffineMetricTest q.left.toAdd q.right
    (0 : MetricSourceProbe Ω)) x=wickFlatMetric
  have zero : wickNativeAffineMetricTest q.left.toAdd q.right
      (0 : MetricSourceProbe Ω)=0 := by
    simpa only [zero_smul] using wick_native_affine_test_smul
      q.left.toAdd q.right 0 (0 : MetricSourceProbe Ω)
  rw [zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wickOriginalFiniteMetric,wickNativeMetricVariation,tensorEncode]

end AASCKleinGordon
