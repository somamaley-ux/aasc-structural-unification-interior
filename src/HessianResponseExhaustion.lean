import CubicJetGauge
import NormalJetFrameNaturality
import SemanticCurvatureExhaustion

/-! A response on the full independent metric-Hessian space. Gauge invariance
must still be derived from actual coordinate naturality for the original
geometric candidate; it is stated explicitly here, not hidden as completeness. -/
namespace AASCSemanticExhaustion
noncomputable section

def HessianAffine (E : metricHessianSpace → Tensor2) : Prop :=
  (∀ H K, E (H + K) = E H + E K - E 0) ∧
  (∀ r : ℝ, ∀ H, E (r • H) = r • (E H - E 0) + E 0)

def HessianSymmetric (E : metricHessianSpace → Tensor2) : Prop :=
  ∀ H a b, E H a b = E H b a

def HessianCovariant (E : metricHessianSpace → Tensor2) : Prop :=
  ∀ L : LorentzComparison, ∀ H K : metricHessianSpace,
    (K : Tensor4) = pullbackFour L.forward (H : Tensor4) →
      E K = L.forward.transpose * E H * L.forward

def hessianCurvatureResponse (E : metricHessianSpace → Tensor2) (R : curvatureSpace) : Tensor2 :=
  E (normalJetMap R)

theorem hessianCurvatureResponse_affine (E : metricHessianSpace → Tensor2)
    (affine : HessianAffine E) : CurvatureAffine (hessianCurvatureResponse E) := by
  constructor
  · intro R S
    simpa only [hessianCurvatureResponse, map_add, map_zero] using affine.1 (normalJetMap R) (normalJetMap S)
  · intro r R
    simpa only [hessianCurvatureResponse, map_smul, map_zero] using affine.2 r (normalJetMap R)

theorem hessianCurvatureResponse_symmetric (E : metricHessianSpace → Tensor2)
    (symmetric : HessianSymmetric E) : TensorSymmetric (hessianCurvatureResponse E) :=
  fun R a b => symmetric (normalJetMap R) a b

theorem hessianCurvatureResponse_covariant (E : metricHessianSpace → Tensor2)
    (covariant : HessianCovariant E) : TensorCovariant (hessianCurvatureResponse E) := by
  intro L R S hS
  exact covariant L (normalJetMap R) (normalJetMap S) (normalJet_frame_natural L.forward R S hS)

theorem hessian_response_normal_form (E : metricHessianSpace → Tensor2)
    (affine : HessianAffine E) (symmetric : HessianSymmetric E)
    (covariant : HessianCovariant E) (gauge : HessianGaugeInvariant E) :
    ∃ a b c : ℝ, ∀ H : metricHessianSpace,
      E H = a • ricciResponse (curvatureJetMap H) +
        b • scalarMetricResponse (curvatureJetMap H) + c • metric := by
  obtain ⟨a, b, c, h⟩ := semantic_affine_response_normal_form (hessianCurvatureResponse E)
    (hessianCurvatureResponse_affine E affine) (hessianCurvatureResponse_symmetric E symmetric)
    (hessianCurvatureResponse_covariant E covariant)
  refine ⟨a, b, c, ?_⟩
  intro H
  rw [hessian_response_curvature_factorization E gauge H]
  exact h (curvatureJetMap H)

theorem hessian_response_unique_normal_form (E : metricHessianSpace → Tensor2)
    (affine : HessianAffine E) (symmetric : HessianSymmetric E)
    (covariant : HessianCovariant E) (gauge : HessianGaugeInvariant E) :
    ∃! coefficients : ℝ × ℝ × ℝ, ∀ H : metricHessianSpace,
      E H = coefficients.1 • ricciResponse (curvatureJetMap H) +
        coefficients.2.1 • scalarMetricResponse (curvatureJetMap H) + coefficients.2.2 • metric := by
  obtain ⟨a, b, c, h⟩ := hessian_response_normal_form E affine symmetric covariant gauge
  refine ⟨(a, b, c), h, ?_⟩
  rintro ⟨a', b', c'⟩ h'
  have hc := contraction_response_coefficients_unique a' b' c' a b c (fun R => by
    have hr := (h' (normalJetMap R)).symm.trans (h (normalJetMap R))
    simpa only [curvatureJet_normalJet_right_inverse] using hr)
  rcases hc with ⟨rfl, rfl, rfl⟩
  rfl

#print axioms hessianCurvatureResponse_affine
#print axioms hessianCurvatureResponse_symmetric
#print axioms hessianCurvatureResponse_covariant
#print axioms hessian_response_normal_form
#print axioms hessian_response_unique_normal_form
end
end AASCSemanticExhaustion
