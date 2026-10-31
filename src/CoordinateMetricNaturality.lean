import CubicCoordinateJacobian
import ScalarSecondJetCalculus

/-! Independent laws on an arbitrary response to actual metric fields.
These expose the jet-order and naturality requirements of the geometric
handoff. They are not a definition of the full manuscript SameScopeMetric1
predicate and contain no desired curvature expansion or completeness field. -/
namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

abbrev MetricFieldResponse := MetricField → CoordinatePoint → Tensor2

def coordinateMetricPullback (g : MetricField) (F : CoordinatePoint → CoordinatePoint)
    (x : CoordinatePoint) : Tensor2 := fun a b =>
  ∑ i : Fin 4, ∑ j : Fin 4,
    coordinateJacobian F x i a * g (F x) i j * coordinateJacobian F x j b

def SmoothCoordinateAt (F : CoordinatePoint → CoordinatePoint) (p : CoordinatePoint) : Prop :=
  ContDiffAt ℝ ⊤ F p ∧ ∃ e : OpenPartialHomeomorph CoordinatePoint CoordinatePoint,
    p ∈ e.source ∧ (e : CoordinatePoint → CoordinatePoint) = F

def MetricResponseNatural (E : MetricFieldResponse) : Prop :=
  ∀ F p, SmoothCoordinateAt F p → ∀ g,
    E (coordinateMetricPullback g F) p =
      (coordinateJacobian F p).transpose * E g (F p) * coordinateJacobian F p

def MetricTwoJetEqualAt (g h : MetricField) (p : CoordinatePoint) : Prop :=
  g p = h p ∧ (∀ a b, fderiv ℝ (fun x => g x a b) p = fderiv ℝ (fun x => h x a b) p) ∧
    ∀ a b c d, scalarSecondPartial (fun x => g x a b) p c d =
      scalarSecondPartial (fun x => h x a b) p c d

def MetricTwoJetLocal (E : MetricFieldResponse) : Prop :=
  ∀ g h p, MetricTwoJetEqualAt g h p → E g p = E h p

theorem smoothCoordinateAt_of_derivative_equiv (F : CoordinatePoint → CoordinatePoint)
    (p : CoordinatePoint) (A : CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (smooth : ContDiffAt ℝ ⊤ F p) (derivative : HasFDerivAt F A.toContinuousLinearMap p) :
    SmoothCoordinateAt F p := by
  refine ⟨smooth, smooth.toOpenPartialHomeomorph F derivative (by simp), ?_, rfl⟩
  exact smooth.mem_toOpenPartialHomeomorph_source derivative (by simp)

theorem cubicCoordinateMap_smoothCoordinateAt (C : Tensor4) :
    SmoothCoordinateAt (cubicCoordinateMap C) 0 :=
  ⟨(cubicCoordinateMap_smooth C).contDiffAt, cubicCoordinateChart C,
    cubicCoordinateChart_zero_source C, cubicCoordinateChart_map C⟩

theorem translation_smoothCoordinateAt (v p : CoordinatePoint) :
    SmoothCoordinateAt (fun x => x + v) p := by
  apply smoothCoordinateAt_of_derivative_equiv _ p (ContinuousLinearEquiv.refl ℝ CoordinatePoint)
  · fun_prop
  · simpa using (hasFDerivAt_id (𝕜 := ℝ) p).add_const v

theorem translation_coordinate_jacobian (v p : CoordinatePoint) :
    coordinateJacobian (fun x => x + v) p = 1 := by
  ext i a
  have hd := (coordinateProjection i).hasFDerivAt (x := p) |>.add_const (v i)
  change HasFDerivAt (fun x : CoordinatePoint => x i + v i) (coordinateProjection i) p at hd
  unfold coordinateJacobian
  change fderiv ℝ (fun x : CoordinatePoint => x i + v i) p (Pi.single a 1) = _
  rw [hd.fderiv]
  simp [coordinateProjection, Pi.single_apply, Matrix.one_apply, eq_comm]

theorem translation_metric_pullback (g : MetricField) (v : CoordinatePoint) :
    coordinateMetricPullback g (fun x => x + v) = (fun x => g (x + v)) := by
  funext x a b
  simp [coordinateMetricPullback, translation_coordinate_jacobian, Matrix.one_apply,
    ite_mul, mul_ite]

theorem metric_response_translation (E : MetricFieldResponse) (natural : MetricResponseNatural E)
    (g : MetricField) (p v : CoordinatePoint) :
    E (fun x => g (x + v)) p = E g (p + v) := by
  have h := natural (fun x => x + v) p (translation_smoothCoordinateAt v p) g
  simpa only [translation_metric_pullback, translation_coordinate_jacobian,
    Matrix.transpose_one, one_mul, mul_one] using h

#print axioms smoothCoordinateAt_of_derivative_equiv
#print axioms cubicCoordinateMap_smoothCoordinateAt
#print axioms translation_smoothCoordinateAt
#print axioms translation_coordinate_jacobian
#print axioms translation_metric_pullback
#print axioms metric_response_translation
end
end AASCSemanticExhaustion
