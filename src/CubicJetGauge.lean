import MetricHessianSpace

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0

/-- The lowered third derivative of a coordinate change is symmetric in its
three coordinate arguments. This is independent of the curvature conclusion. -/
def CubicCoordinateLaws (T : Tensor4) : Prop :=
  (∀ a b c d, T a b c d = T a c b d) ∧
  (∀ a b c d, T a b c d = T a b d c)

def HasCubicCoordinateGauge (H : metricHessianSpace) : Prop :=
  ∃ T : Tensor4, CubicCoordinateLaws T ∧
    ∀ a b c d, (H : Tensor4) a b c d = T a b c d + T b a c d

def hessianConnectionDerivative (H : metricHessianSpace) (a b c d : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * ((H : Tensor4) a c b d + (H : Tensor4) a b c d - (H : Tensor4) b c a d)

theorem hessianConnectionDerivative_torsion (H : metricHessianSpace) (a b c d : Fin 4) :
    hessianConnectionDerivative H a b c d = hessianConnectionDerivative H a c b d := by
  unfold hessianConnectionDerivative
  rw [H.property.1 c b a d]
  ring

theorem hessian_metric_reconstruction (H : metricHessianSpace) (a b c d : Fin 4) :
    (H : Tensor4) a b c d =
      hessianConnectionDerivative H a b c d + hessianConnectionDerivative H b a c d := by
  unfold hessianConnectionDerivative
  rw [H.property.1 b a c d]
  ring

theorem hessian_curvature_connection_formula (H : metricHessianSpace) (a b c d : Fin 4) :
    curvatureOfNormalHessian H a b c d =
      hessianConnectionDerivative H a d b c - hessianConnectionDerivative H a c b d := by
  unfold curvatureOfNormalHessian hessianConnectionDerivative
  rw [H.property.2 a b d c, H.property.1 d b a c, H.property.1 c b a d]
  ring

theorem flat_hessian_connection_cubic (H : metricHessianSpace)
    (flat : curvatureJetMap H = 0) : CubicCoordinateLaws (hessianConnectionDerivative H) := by
  refine ⟨hessianConnectionDerivative_torsion H, ?_⟩
  intro a b c d
  have hflat : curvatureOfNormalHessian H a b c d = 0 :=
    congrArg (fun R : curvatureSpace => (R : Tensor4) a b c d) flat
  rw [hessian_curvature_connection_formula] at hflat
  rw [hessianConnectionDerivative_torsion H a d b c,
    hessianConnectionDerivative_torsion H a c b d] at hflat
  exact (sub_eq_zero.mp hflat).symm

theorem flat_hessian_has_cubic_coordinate_gauge (H : metricHessianSpace)
    (flat : curvatureJetMap H = 0) : HasCubicCoordinateGauge H :=
  ⟨hessianConnectionDerivative H, flat_hessian_connection_cubic H flat,
    hessian_metric_reconstruction H⟩

theorem cubic_coordinate_gauge_flat (H : metricHessianSpace)
    (gauge : HasCubicCoordinateGauge H) : curvatureJetMap H = 0 := by
  obtain ⟨T, ht, heq⟩ := gauge
  apply Subtype.ext
  funext a b c d
  change curvatureOfNormalHessian H a b c d = 0
  unfold curvatureOfNormalHessian
  rw [heq a d b c, heq b c a d, heq a c b d, heq b d a c]
  linarith [ht.1 a d b c, ht.2 a b d c, ht.1 a b c d, ht.1 d a b c,
    ht.1 b c a d, ht.2 b a c d, ht.1 b a d c, ht.1 c b a d]

theorem curvature_kernel_iff_cubic_coordinate_gauge (H : metricHessianSpace) :
    curvatureJetMap H = 0 ↔ HasCubicCoordinateGauge H :=
  ⟨flat_hessian_has_cubic_coordinate_gauge H, cubic_coordinate_gauge_flat H⟩

theorem hessian_normal_residual_is_gauge (H : metricHessianSpace) :
    HasCubicCoordinateGauge (H - normalJetMap (curvatureJetMap H)) := by
  apply flat_hessian_has_cubic_coordinate_gauge
  rw [map_sub, curvatureJet_normalJet_right_inverse, sub_self]

/-- A response law under independently specified cubic coordinate gauge.
Its derivation from actual local coordinate changes remains a geometric step. -/
def HessianGaugeInvariant (E : metricHessianSpace → Tensor2) : Prop :=
  ∀ H K, HasCubicCoordinateGauge K → E (H + K) = E H

theorem hessian_response_curvature_factorization (E : metricHessianSpace → Tensor2)
    (gaugeInvariant : HessianGaugeInvariant E) (H : metricHessianSpace) :
    E H = E (normalJetMap (curvatureJetMap H)) := by
  have h := gaugeInvariant (normalJetMap (curvatureJetMap H))
    (H - normalJetMap (curvatureJetMap H)) (hessian_normal_residual_is_gauge H)
  have heq : normalJetMap (curvatureJetMap H) + (H - normalJetMap (curvatureJetMap H)) = H := by abel
  rw [heq] at h
  exact h

#print axioms hessianConnectionDerivative_torsion
#print axioms hessian_metric_reconstruction
#print axioms hessian_curvature_connection_formula
#print axioms flat_hessian_connection_cubic
#print axioms flat_hessian_has_cubic_coordinate_gauge
#print axioms cubic_coordinate_gauge_flat
#print axioms curvature_kernel_iff_cubic_coordinate_gauge
#print axioms hessian_normal_residual_is_gauge
#print axioms hessian_response_curvature_factorization
end
end AASCSemanticExhaustion
