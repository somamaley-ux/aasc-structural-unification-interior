import CoordinateVectorSecondJet

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

theorem c2_local_scalarPartial_mul (f h : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (hf : ContDiffAt ℝ 2 f p) (hh : ContDiffAt ℝ 2 h p) (c : Fin 4) :
    scalarPartial (fun x => f x * h x) p c =
      f p * scalarPartial h p c + h p * scalarPartial f p c := by
  have hd := ((hf.differentiableAt (by norm_num)).hasFDerivAt.mul
    (hh.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  change fderiv ℝ (fun x => f x * h x) p = _ at hd
  simp only [scalarPartial, hd, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem c2_local_scalarSecondPartial_triple (f h k : CoordinatePoint → ℝ)
    (hf : ContDiffAt ℝ 2 f 0) (hh : ContDiffAt ℝ 2 h 0) (hk : ContDiffAt ℝ 2 k 0) (c d : Fin 4) :
    scalarSecondPartial (fun x => f x * h x * k x) 0 c d =
      f 0 * h 0 * scalarSecondPartial k 0 c d +
        f 0 * k 0 * scalarSecondPartial h 0 c d + h 0 * k 0 * scalarSecondPartial f 0 c d +
        k 0 * (scalarPartial f 0 c * scalarPartial h 0 d + scalarPartial h 0 c * scalarPartial f 0 d) +
        h 0 * (scalarPartial f 0 c * scalarPartial k 0 d + scalarPartial k 0 c * scalarPartial f 0 d) +
        f 0 * (scalarPartial h 0 c * scalarPartial k 0 d + scalarPartial k 0 c * scalarPartial h 0 d) := by
  rw [c2_local_scalarSecondPartial_mul (fun x => f x * h x) k 0 (hf.mul hh) hk,
    c2_local_scalarSecondPartial_mul f h 0 hf hh,
    c2_local_scalarPartial_mul f h 0 hf hh c,
    c2_local_scalarPartial_mul f h 0 hf hh d]
  ring

theorem c2_quadratic_identity_composition_first (f : CoordinatePoint → ℝ)
    (regular : ContDiffAt ℝ 2 f 0) (Q : CoordinateQuadraticArray) :
    fderiv ℝ (fun x => f (quadraticIdentityMap Q x)) 0 = fderiv ℝ f 0 := by
  have hf : DifferentiableAt ℝ f (quadraticIdentityMap Q 0) := by
    simpa only [quadraticIdentityMap_zero] using regular.differentiableAt (by norm_num)
  have hd := hf.hasFDerivAt.comp 0 (quadraticCoordinateMap_hasFDerivAt_zero 0
    (ContinuousLinearEquiv.refl ℝ CoordinatePoint) Q)
  change HasFDerivAt (fun x => f (quadraticIdentityMap Q x))
    ((fderiv ℝ f (quadraticIdentityMap Q 0)).comp (ContinuousLinearMap.id ℝ CoordinatePoint)) 0 at hd
  simpa only [quadraticIdentityMap_zero, ContinuousLinearMap.comp_id] using hd.fderiv

theorem c2_quadratic_identity_composition_second (f : CoordinatePoint → ℝ)
    (regular : ContDiffAt ℝ 2 f 0) (Q : CoordinateQuadraticArray)
    (symmetric : ∀ i a b, Q i a b = Q i b a) (c d : Fin 4) :
    scalarSecondPartial (fun x => f (quadraticIdentityMap Q x)) 0 c d =
      scalarSecondPartial f 0 c d + ∑ i : Fin 4, scalarPartial f 0 i * Q i c d := by
  have hf : ContDiffAt ℝ 2 f (quadraticIdentityMap Q 0) := by
    simpa only [quadraticIdentityMap_zero] using regular
  have hDF : fderiv ℝ (quadraticIdentityMap Q) 0 = ContinuousLinearMap.id ℝ CoordinatePoint :=
    (quadraticCoordinateMap_hasFDerivAt_zero 0 (ContinuousLinearEquiv.refl ℝ CoordinatePoint) Q).fderiv
  rw [c2_local_scalarSecondPartial_comp f (quadraticIdentityMap Q) 0 hf
    ((quadraticCoordinateMap_smooth _ _ _).contDiffAt.of_le (by simp)),
    quadraticIdentityMap_zero, quadratic_identity_vector_second_derivative Q symmetric, hDF]
  have h := continuousLinearMap_four_coordinates (fderiv ℝ f 0).toLinearMap (fun i => Q i c d)
  change fderiv ℝ f 0 (fun i => Q i c d) = ∑ i : Fin 4, Q i c d * scalarPartial f 0 i at h
  rw [h, c2_scalarSecondPartial_full_second_derivative f 0 regular]
  simp only [ContinuousLinearEquiv.refl_apply, ContinuousLinearMap.id_apply]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The full actual second metric jet under a quadratic identity-first-jet chart. -/
theorem c2_quadratic_identity_metric_second (g : MetricField)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) 0)
    (Q : CoordinateQuadraticArray) (symmetric : ∀ i a b, Q i a b = Q i b a) (a b c d : Fin 4) :
    scalarSecondPartial (fun x => coordinateMetricPullback g (quadraticIdentityMap Q) x a b) 0 c d =
      scalarSecondPartial (fun x => g x a b) 0 c d +
        (∑ u : Fin 4, metricPartial g 0 a b u * Q u c d) +
        (∑ i : Fin 4, (Q i a c * metricPartial g 0 i b d + metricPartial g 0 i b c * Q i a d)) +
        (∑ j : Fin 4, (metricPartial g 0 a j c * Q j b d + Q j b c * metricPartial g 0 a j d)) +
        (∑ i : Fin 4, ∑ j : Fin 4, g 0 i j * (Q i a c * Q j b d + Q j b c * Q i a d)) := by
  let F := quadraticIdentityMap Q
  let J := fun i k x => coordinateJacobian F x i k
  let B := fun i j x => g (F x) i j
  let W := fun i j x => J i a x * B i j x * J j b x
  have hF : ContDiffAt ℝ 3 F 0 := (quadraticCoordinateMap_smooth _ _ _).contDiffAt.of_le (by simp)
  have hj (i k : Fin 4) : ContDiffAt ℝ 2 (J i k) 0 := c3_coordinateJacobian_c2 F 0 hF i k
  have hb (i j : Fin 4) : ContDiffAt ℝ 2 (B i j) 0 := by
    have hs : ContDiffAt ℝ 2 (fun x => g x i j) (F 0) := by
      simpa only [F, quadraticIdentityMap_zero] using regular i j
    exact hs.comp 0 (hF.of_le (by norm_num))
  have hw (i j : Fin 4) : ContDiffAt ℝ 2 (W i j) 0 := ((hj i a).mul (hb i j)).mul (hj j b)
  have hj0 (i k : Fin 4) : J i k 0 = (1 : Tensor2) i k :=
    congrArg (fun M : Tensor2 => M i k) (quadraticIdentityMap_jacobian_zero Q symmetric)
  have hb0 (i j : Fin 4) : B i j 0 = g 0 i j := by simp [B, F, quadraticIdentityMap_zero]
  have hj1 (i k r : Fin 4) : scalarPartial (J i k) 0 r = Q i k r := by
    unfold scalarPartial
    change fderiv ℝ (fun x => coordinateJacobian (quadraticCoordinateMap 0
      (ContinuousLinearEquiv.refl ℝ CoordinatePoint) Q) x i k) 0 (Pi.single r 1) = _
    rw [(quadraticJacobian_hasFDerivAt 0 (ContinuousLinearEquiv.refl ℝ CoordinatePoint)
      Q symmetric 0 i k).fderiv, quadraticJacobianDerivative_basis]
  have hb1 (i j r : Fin 4) : scalarPartial (B i j) 0 r = metricPartial g 0 i j r := by
    unfold scalarPartial
    rw [c2_quadratic_identity_composition_first _ (regular i j) Q]
    rfl
  have hj2 (i k : Fin 4) : scalarSecondPartial (J i k) 0 c d = 0 :=
    quadratic_coordinate_jacobian_second_zero _ _ Q symmetric i k c d
  have hb2 (i j : Fin 4) : scalarSecondPartial (B i j) 0 c d =
      scalarSecondPartial (fun x => g x i j) 0 c d +
        ∑ u : Fin 4, metricPartial g 0 i j u * Q u c d :=
    c2_quadratic_identity_composition_second _ (regular i j) Q symmetric c d
  have hW (i j : Fin 4) := c2_local_scalarSecondPartial_triple (J i a) (B i j) (J j b)
    (hj i a) (hb i j) (hj j b) c d
  simp only [hj0, hb0, hj1, hb1, hj2, hb2, mul_zero, zero_mul, add_zero, zero_add] at hW
  have ho (i : Fin 4) : ContDiffAt ℝ 2 (fun x => ∑ j, W i j x) 0 := ContDiffAt.sum (fun j _ => hw i j)
  change scalarSecondPartial (fun x => ∑ i : Fin 4, ∑ j : Fin 4, W i j x) 0 c d = _
  rw [c2_local_scalarSecondPartial_sum _ 0 ho c d]
  simp_rw [c2_local_scalarSecondPartial_sum _ 0 (hw _) c d]
  dsimp only [W]
  simp_rw [hW]
  simp [Matrix.one_apply, ite_mul, mul_ite, Finset.sum_add_distrib, mul_add, add_mul]
  ring

#print axioms c2_local_scalarPartial_mul
#print axioms c2_local_scalarSecondPartial_triple
#print axioms c2_quadratic_identity_composition_first
#print axioms c2_quadratic_identity_composition_second
#print axioms c2_quadratic_identity_metric_second
end
end AASCSemanticExhaustion
