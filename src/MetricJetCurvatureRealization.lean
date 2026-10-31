import AlgebraicCurvatureCoordinates

/-!
Algebraic second-jet realization step. This constructs the candidate Hessian
and proves its symmetries and curvature formula from the original curvature
laws. It does not yet construct a smooth metric on a neighborhood, prove the
geometric Levi-Civita formula, or factor an original local response through jets.
-/
namespace AASCSemanticExhaustion
noncomputable section

def normalMetricHessian (R : curvatureSpace) (a b c d : Fin 4) : ℝ :=
  -(1 / 3 : ℝ) * ((R : Tensor4) a c b d + (R : Tensor4) a d b c)

def curvatureOfNormalHessian (H : Tensor4) (a b c d : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * (H a d b c + H b c a d - H a c b d - H b d a c)

theorem normalMetricHessian_metric_symmetry (R : curvatureSpace) (a b c d : Fin 4) :
    normalMetricHessian R a b c d = normalMetricHessian R b a c d := by
  unfold normalMetricHessian
  rw [R.property.2.2.1 b c a d, R.property.2.2.1 b d a c]
  ring

theorem normalMetricHessian_derivative_symmetry (R : curvatureSpace) (a b c d : Fin 4) :
    normalMetricHessian R a b c d = normalMetricHessian R a b d c := by
  unfold normalMetricHessian
  ring

theorem curvature_of_constructed_normal_hessian (R : curvatureSpace) :
    curvatureOfNormalHessian (normalMetricHessian R) = (R : Tensor4) := by
  funext a b c d
  unfold curvatureOfNormalHessian normalMetricHessian
  linarith [R.property.2.1 a b c d, R.property.1 b a c d,
    R.property.1 b a d c, R.property.2.2.1 b d c a,
    R.property.1 c a b d, R.property.2.1 a c d b,
    R.property.2.2.1 b c d a, R.property.1 d a b c,
    R.property.2.1 a d c b, R.property.2.2.2 a b c d]

theorem algebraic_normal_jet_curvature_surjective (R : curvatureSpace) :
    ∃ H : Tensor4,
      (∀ a b c d, H a b c d = H b a c d) ∧
      (∀ a b c d, H a b c d = H a b d c) ∧
      curvatureOfNormalHessian H = (R : Tensor4) :=
  ⟨normalMetricHessian R, normalMetricHessian_metric_symmetry R,
    normalMetricHessian_derivative_symmetry R,
    curvature_of_constructed_normal_hessian R⟩

#print axioms normalMetricHessian_metric_symmetry
#print axioms normalMetricHessian_derivative_symmetry
#print axioms curvature_of_constructed_normal_hessian
#print axioms algebraic_normal_jet_curvature_surjective
end
end AASCSemanticExhaustion
