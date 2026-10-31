import MetricJetCurvatureRealization

/-! Independent normal metric Hessians. This space contains every array with
metric-index and derivative-index symmetry, not a curvature-expression syntax. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0

def MetricHessianLaws (H : Tensor4) : Prop :=
  (∀ a b c d, H a b c d = H b a c d) ∧ (∀ a b c d, H a b c d = H a b d c)

def metricHessianSpace : Submodule ℝ Tensor4 where
  carrier := {H | MetricHessianLaws H}
  zero_mem' := by simp [MetricHessianLaws]
  add_mem' := by
    intro H K hH hK
    constructor
    · intro a b c d
      change H a b c d + K a b c d = H b a c d + K b a c d
      rw [hH.1 a b c d, hK.1 a b c d]
    · intro a b c d
      change H a b c d + K a b c d = H a b d c + K a b d c
      rw [hH.2 a b c d, hK.2 a b c d]
  smul_mem' := by
    intro r H hH
    constructor
    · intro a b c d
      change r * H a b c d = r * H b a c d
      rw [hH.1 a b c d]
    · intro a b c d
      change r * H a b c d = r * H a b d c
      rw [hH.2 a b c d]

theorem normalMetricHessian_mem (R : curvatureSpace) :
    normalMetricHessian R ∈ metricHessianSpace :=
  ⟨normalMetricHessian_metric_symmetry R, normalMetricHessian_derivative_symmetry R⟩

theorem hessian_curvature_skew_first (H : metricHessianSpace) (a b c d : Fin 4) :
    curvatureOfNormalHessian H a b c d = -curvatureOfNormalHessian H b a c d := by
  unfold curvatureOfNormalHessian
  ring

theorem hessian_curvature_skew_last (H : metricHessianSpace) (a b c d : Fin 4) :
    curvatureOfNormalHessian H a b c d = -curvatureOfNormalHessian H a b d c := by
  unfold curvatureOfNormalHessian
  ring

theorem hessian_curvature_pair_exchange (H : metricHessianSpace) (a b c d : Fin 4) :
    curvatureOfNormalHessian H a b c d = curvatureOfNormalHessian H c d a b := by
  unfold curvatureOfNormalHessian
  rw [H.property.1 c b d a, H.property.2 b c d a,
    H.property.1 d a c b, H.property.2 a d c b,
    H.property.1 c a d b, H.property.2 a c d b,
    H.property.1 d b c a, H.property.2 b d c a]
  ring

theorem hessian_curvature_bianchi (H : metricHessianSpace) (a b c d : Fin 4) :
    curvatureOfNormalHessian H a b c d + curvatureOfNormalHessian H a c d b +
      curvatureOfNormalHessian H a d b c = 0 := by
  unfold curvatureOfNormalHessian
  rw [H.property.2 a d c b, H.property.2 a b d c, H.property.2 a c d b,
    H.property.1 c d a b, H.property.1 c b a d, H.property.1 d b a c]
  ring

theorem hessian_curvature_mem (H : metricHessianSpace) :
    curvatureOfNormalHessian H ∈ curvatureSpace :=
  ⟨hessian_curvature_skew_first H, hessian_curvature_skew_last H,
    hessian_curvature_pair_exchange H, hessian_curvature_bianchi H⟩

def curvatureJetMap : metricHessianSpace →ₗ[ℝ] curvatureSpace where
  toFun H := ⟨curvatureOfNormalHessian H, hessian_curvature_mem H⟩
  map_add' H K := by
    apply Subtype.ext
    funext a b c d
    simp only [curvatureOfNormalHessian, Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' r H := by
    apply Subtype.ext
    funext a b c d
    simp only [curvatureOfNormalHessian, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def normalJetMap : curvatureSpace →ₗ[ℝ] metricHessianSpace where
  toFun R := ⟨normalMetricHessian R, normalMetricHessian_mem R⟩
  map_add' R S := by
    apply Subtype.ext
    funext a b c d
    simp only [normalMetricHessian, Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' r R := by
    apply Subtype.ext
    funext a b c d
    simp only [normalMetricHessian, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem curvatureJet_normalJet_right_inverse (R : curvatureSpace) :
    curvatureJetMap (normalJetMap R) = R :=
  Subtype.ext (curvature_of_constructed_normal_hessian R)

theorem curvatureJetMap_surjective : Function.Surjective curvatureJetMap :=
  fun R => ⟨normalJetMap R, curvatureJet_normalJet_right_inverse R⟩

#print axioms normalMetricHessian_mem
#print axioms hessian_curvature_skew_first
#print axioms hessian_curvature_skew_last
#print axioms hessian_curvature_pair_exchange
#print axioms hessian_curvature_bianchi
#print axioms hessian_curvature_mem
#print axioms curvatureJet_normalJet_right_inverse
#print axioms curvatureJetMap_surjective
end
end AASCSemanticExhaustion
