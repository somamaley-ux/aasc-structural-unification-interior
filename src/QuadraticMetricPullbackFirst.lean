import MetricPullbackRegularity

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

def quadraticIdentityMap (Q : CoordinateQuadraticArray) : CoordinatePoint → CoordinatePoint :=
  quadraticCoordinateMap 0 (ContinuousLinearEquiv.refl ℝ CoordinatePoint) Q

theorem quadraticIdentityMap_zero (Q : CoordinateQuadraticArray) : quadraticIdentityMap Q 0 = 0 :=
  quadraticCoordinateMap_zero _ _ _

theorem quadraticIdentityMap_jacobian_zero (Q : CoordinateQuadraticArray)
    (symmetric : ∀ i a b, Q i a b = Q i b a) :
    coordinateJacobian (quadraticIdentityMap Q) 0 = 1 := by
  rw [quadraticIdentityMap, quadraticCoordinateMap_jacobian_zero _ _ _ symmetric, coordinateFrameMatrix_refl]

theorem quadratic_identity_metric_pullback_partial (g : MetricField)
    (smooth : ∀ a b, ContDiffAt ℝ ⊤ (fun x => g x a b) 0)
    (Q : CoordinateQuadraticArray) (symmetric : ∀ i a b, Q i a b = Q i b a)
    (a b c : Fin 4) :
    scalarPartial (fun x => coordinateMetricPullback g (quadraticIdentityMap Q) x a b) 0 c =
      metricPartial g 0 a b c + (∑ i : Fin 4, g 0 i b * Q i a c) + (∑ j : Fin 4, g 0 a j * Q j b c) := by
  let F := quadraticIdentityMap Q
  have hF : HasFDerivAt F (ContinuousLinearMap.id ℝ CoordinatePoint) 0 :=
    quadraticCoordinateMap_hasFDerivAt_zero _ _ _
  have hfzero : F 0 = 0 := quadraticIdentityMap_zero Q
  have hjzero : coordinateJacobian F 0 = 1 := quadraticIdentityMap_jacobian_zero Q symmetric
  have hj (i k : Fin 4) : HasFDerivAt (fun x => coordinateJacobian F x i k)
      (quadraticJacobianDerivative Q i k) 0 :=
    quadraticJacobian_hasFDerivAt _ _ _ symmetric 0 i k
  have hb (i j : Fin 4) : HasFDerivAt (fun x => g (F x) i j)
      (fderiv ℝ (fun x => g x i j) 0) 0 := by
    have hdg : DifferentiableAt ℝ (fun x => g x i j) (F 0) := by
      simpa only [hfzero] using (smooth i j).differentiableAt (by simp)
    have hd := hdg.hasFDerivAt.comp 0 hF
    change HasFDerivAt (fun x => g (F x) i j)
      ((fderiv ℝ (fun x => g x i j) (F 0)).comp (ContinuousLinearMap.id ℝ CoordinatePoint)) 0 at hd
    simpa only [hfzero, ContinuousLinearMap.comp_id] using hd
  have ht (i j : Fin 4) := ((hj i a).mul (hb i j)).mul (hj j b)
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => ht i j))
  simp only [Pi.mul_apply, hfzero, hjzero] at hs
  have hd := hs.fderiv
  change fderiv ℝ (fun x => coordinateMetricPullback g F x a b) 0 = _ at hd
  unfold scalarPartial
  change fderiv ℝ (fun x => coordinateMetricPullback g F x a b) 0 (Pi.single c 1) = _
  rw [hd]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, smul_eq_mul, quadraticJacobianDerivative_basis]
  change (∑ i : Fin 4, ∑ j : Fin 4,
    (((1 : Tensor2) i a * g 0 i j) * Q j b c + (1 : Tensor2) j b *
      ((1 : Tensor2) i a * metricPartial g 0 i j c + g 0 i j * Q i a c))) = _
  simp [Matrix.one_apply, Finset.sum_add_distrib, mul_add, ite_mul, mul_ite]
  ring

theorem continuousLinearMap_zero_of_coordinate_basis (D : CoordinatePoint →L[ℝ] ℝ)
    (zero : ∀ c : Fin 4, D (Pi.single c 1) = 0) : D = 0 := by
  ext v
  have h := continuousLinearMap_four_coordinates D.toLinearMap v
  change D v = ∑ i : Fin 4, v i • D (Pi.single i 1) at h
  simpa only [zero, smul_zero, Finset.sum_const_zero, ContinuousLinearMap.zero_apply] using h

#print axioms quadraticIdentityMap_zero
#print axioms quadraticIdentityMap_jacobian_zero
#print axioms quadratic_identity_metric_pullback_partial
#print axioms continuousLinearMap_zero_of_coordinate_basis
end
end AASCSemanticExhaustion
