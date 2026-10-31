import MetricPullbackRegularity
import Mathlib.Topology.OpenPartialHomeomorph.Composition

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

theorem fderiv_vector_component (F : CoordinatePoint → CoordinatePoint) (x : CoordinatePoint)
    (differentiable : DifferentiableAt ℝ F x) (v : CoordinatePoint) (i : Fin 4) :
    fderiv ℝ (fun y => F y i) x v = fderiv ℝ F x v i := by
  have hd := (coordinateProjection i).hasFDerivAt.comp x differentiable.hasFDerivAt
  change HasFDerivAt (fun y => F y i) ((coordinateProjection i).comp (fderiv ℝ F x)) x at hd
  rw [hd.fderiv]
  rfl

theorem coordinateJacobian_vector (F : CoordinatePoint → CoordinatePoint) (x : CoordinatePoint)
    (differentiable : DifferentiableAt ℝ F x) (i a : Fin 4) :
    coordinateJacobian F x i a = fderiv ℝ F x (Pi.single a 1) i :=
  fderiv_vector_component F x differentiable _ i

theorem coordinateJacobian_comp (F G : CoordinatePoint → CoordinatePoint) (x : CoordinatePoint)
    (hF : DifferentiableAt ℝ F (G x)) (hG : DifferentiableAt ℝ G x) :
    coordinateJacobian (fun y => F (G y)) x = coordinateJacobian F (G x) * coordinateJacobian G x := by
  ext i a
  have hc := hF.hasFDerivAt.comp x hG.hasFDerivAt
  have hd := (coordinateProjection i).hasFDerivAt.comp x hc
  change HasFDerivAt (fun y => F (G y) i)
    ((coordinateProjection i).comp ((fderiv ℝ F (G x)).comp (fderiv ℝ G x))) x at hd
  unfold coordinateJacobian
  rw [hd.fderiv]
  have h := continuousLinearMap_four_coordinates
    ((coordinateProjection i).comp (fderiv ℝ F (G x))).toLinearMap (fderiv ℝ G x (Pi.single a 1))
  change fderiv ℝ F (G x) (fderiv ℝ G x (Pi.single a 1)) i =
    ∑ j : Fin 4, (fderiv ℝ G x (Pi.single a 1)) j * (fderiv ℝ F (G x) (Pi.single j 1)) i at h
  simp only [Matrix.mul_apply]
  simpa only [ContinuousLinearMap.comp_apply, coordinateProjection, ContinuousLinearMap.proj_apply,
    fderiv_vector_component F (G x) hF, fderiv_vector_component G x hG, mul_comm] using h

theorem coordinateMetricPullback_matrix (g : MetricField) (F : CoordinatePoint → CoordinatePoint)
    (x : CoordinatePoint) :
    coordinateMetricPullback g F x = (coordinateJacobian F x).transpose * g (F x) * coordinateJacobian F x := by
  ext a b
  exact matrix_pullback_double_sum _ _ a b

theorem coordinateMetricPullback_comp (g : MetricField) (F G : CoordinatePoint → CoordinatePoint)
    (smoothF : ContDiff ℝ ⊤ F) (smoothG : ContDiff ℝ ⊤ G) :
    coordinateMetricPullback (coordinateMetricPullback g F) G =
      coordinateMetricPullback g (fun x => F (G x)) := by
  funext x
  rw [coordinateMetricPullback_matrix (coordinateMetricPullback g F) G x,
    coordinateMetricPullback_matrix g F (G x),
    coordinateMetricPullback_matrix g (fun x => F (G x)) x,
    coordinateJacobian_comp F G x (smoothF.differentiable (by simp) (G x))
      (smoothG.differentiable (by simp) x)]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

theorem smoothCoordinateAt_comp (F G : CoordinatePoint → CoordinatePoint) (p : CoordinatePoint)
    (hF : SmoothCoordinateAt F (G p)) (hG : SmoothCoordinateAt G p) :
    SmoothCoordinateAt (fun x => F (G x)) p := by
  obtain ⟨sF, eF, hpF, heF⟩ := hF
  obtain ⟨sG, eG, hpG, heG⟩ := hG
  refine ⟨sF.comp p sG, eG.trans eF, ?_, ?_⟩
  · exact ⟨hpG, by simpa [heG] using hpF⟩
  · change (fun x => eF (eG x)) = (fun x => F (G x))
    rw [heF, heG]

#print axioms fderiv_vector_component
#print axioms coordinateJacobian_vector
#print axioms coordinateJacobian_comp
#print axioms coordinateMetricPullback_matrix
#print axioms coordinateMetricPullback_comp
#print axioms smoothCoordinateAt_comp
end
end AASCSemanticExhaustion
