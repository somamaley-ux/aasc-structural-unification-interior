import WickPoincareProtocolTransport
import WickTransportedMetricSignature

noncomputable section
set_option maxHeartbeats 1500000
open TopologicalSpace Filter
open scoped Topology Matrix.Norms.Operator
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem wick_KG_metinc_first {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω)
    (δ : WickKGFirstMetricAct Ω) :
    wickKGOriginalMetInc H (.first δ) ↔ wickKGFirstTangent δ=H := by
  constructor
  · rintro ⟨ε,incident,tangent⟩
    have same : δ=ε := WickKGOriginalProtocol.first.inj incident
    subst ε
    exact tangent
  · intro tangent
    exact ⟨δ,rfl,tangent⟩

theorem wick_KG_metinc_finite {Ω : Opens CoordinatePoint} (H K : MetricSourceProbe Ω) :
    ¬wickKGOriginalMetInc H (.finite K) := by
  rintro ⟨δ,incident,_⟩
  cases incident

theorem wick_KG_incidence_poincare (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω) (π : WickKGOriginalProtocol Ω) :
    wickKGOriginalMetInc (wickNativeAffineMetricTest b L H) (wickKGProtocolPoincare b L π) ↔
      wickKGOriginalMetInc H π := by
  cases π with
  | finite K =>
    constructor
    · intro h
      exact False.elim (wick_KG_metinc_finite _ _ h)
    · intro h
      exact False.elim (wick_KG_metinc_finite _ _ h)
  | first δ =>
    change wickKGOriginalMetInc (wickNativeAffineMetricTest b L H)
      (.first (wickKGFirstActPoincare b L δ)) ↔ _
    rw [wick_KG_metinc_first, wick_KG_metinc_first, wick_KG_poincare_tangent]
    constructor
    · intro h
      exact wick_native_affine_test_injective b L Ω h
    · exact congrArg (wickNativeAffineMetricTest b L)

theorem wick_KG_poincare_act_metric_curve (b : Spacetime) (L : ProperLorentzTransform)
    {Ω : Opens CoordinatePoint} (δ : WickKGFirstMetricAct Ω) (t : ℝ) (x : Spacetime) :
    wickKGFirstMetricCurve (wickKGFirstActPoincare b L δ) t (b+spacetimeLorentzCLE L x)=
      (wickLorentzMatrix L⁻¹).transpose*wickKGFirstMetricCurve δ t x*wickLorentzMatrix L⁻¹ := by
  change wickOriginalFiniteMetric (δ.parameter t • wickNativeAffineMetricTest b L δ.test)
    (b+spacetimeLorentzCLE L x)=_
  rw [← wick_native_affine_test_smul, wick_native_affine_finite_metric]
  rfl

theorem wick_KG_poincare_act_admitted (b : Spacetime) (L : ProperLorentzTransform)
    {Ω : Opens CoordinatePoint} (δ : WickKGFirstMetricAct Ω) :
    ∀ᶠ t in 𝓝 0,δ.parameter t • wickNativeAffineMetricTest b L δ.test ∈
      wickTransportedMetricDomain b L Ω := by
  filter_upwards [wick_KG_original_act_admitted δ] with t inside
  rw [← wick_native_affine_test_smul]
  exact (wick_transported_metric_domain_exact b L Ω _).mpr inside

theorem wick_transported_metric_smooth_and_symmetric (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) (J : MetricSourceProbe (wickAffineMetricRegion b L Ω)) :
    ContDiff ℝ (⊤ : ℕ∞) (wickOriginalFiniteMetric J) ∧
      ∀ y i j,wickOriginalFiniteMetric J y i j=wickOriginalFiniteMetric J y j i :=
  ⟨wick_original_finite_metric_smooth J,wick_original_finite_metric_symmetric J⟩

theorem wick_KG_poincare_act_intrinsic_signature (b : Spacetime) (L : ProperLorentzTransform)
    {Ω : Opens CoordinatePoint} (δ : WickKGFirstMetricAct Ω) :
    ∀ᶠ t in 𝓝 0,∀ y,
      WickIntrinsicLorentzSignature (wickKGFirstMetricCurve (wickKGFirstActPoincare b L δ) t y) ∧
        (wickKGFirstMetricCurve (wickKGFirstActPoincare b L δ) t y).det≠0 := by
  filter_upwards [wick_KG_poincare_act_admitted b L δ] with t inside
  intro y
  exact wick_transported_metric_signature b L Ω _ inside y

end AASCKleinGordon
