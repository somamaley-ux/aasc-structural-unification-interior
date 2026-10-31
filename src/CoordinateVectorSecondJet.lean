import C2GeneralCurvatureFormula

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0

theorem coordinate_vector_second_derivative_component (F : CoordinatePoint → CoordinatePoint)
    (p : CoordinatePoint) (regular : ContDiffAt ℝ 2 F p) (i c d : Fin 4) :
    fderiv ℝ (fderiv ℝ F) p (Pi.single d 1) (Pi.single c 1) i =
      scalarSecondPartial (fun x => F x i) p c d := by
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) p :=
    (regular.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hv := hdF.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single c (1 : ℝ) : CoordinatePoint) p)
  have hi := (coordinateProjection i).hasFDerivAt.comp p hv
  have he : ∀ᶠ x in nhds p,
      scalarPartial (fun y => F y i) x c = fderiv ℝ F x (Pi.single c 1) i := by
    have hs := regular.eventually (by norm_num)
    filter_upwards [hs] with x hx
    exact fderiv_vector_component F x (hx.differentiableAt (by norm_num)) _ i
  have h := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) he
  have hh := hi.fderiv
  change fderiv ℝ (fun x => fderiv ℝ F x (Pi.single c 1) i) p = _ at hh
  rw [hh] at h
  have hval := congrArg (fun D : CoordinatePoint →L[ℝ] ℝ => D (Pi.single d 1)) h
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply,
    coordinateProjection, ContinuousLinearMap.proj_apply] using hval.symm

theorem quadratic_coordinate_jacobian_second_zero (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (Q : CoordinateQuadraticArray)
    (symmetric : ∀ i a b, Q i a b = Q i b a) (i a c d : Fin 4) :
    scalarSecondPartial (fun x => coordinateJacobian (quadraticCoordinateMap p B Q) x i a) 0 c d = 0 := by
  have he : (fun x => scalarPartial
      (fun y => coordinateJacobian (quadraticCoordinateMap p B Q) y i a) x c) =
      (fun _ : CoordinatePoint => Q i a c) := by
    funext x
    unfold scalarPartial
    rw [(quadraticJacobian_hasFDerivAt p B Q symmetric x i a).fderiv,
      quadraticJacobianDerivative_basis]
  unfold scalarSecondPartial
  rw [he]
  simp [scalarPartial]

theorem quadratic_identity_vector_second_derivative (Q : CoordinateQuadraticArray)
    (symmetric : ∀ i a b, Q i a b = Q i b a) (c d : Fin 4) :
    fderiv ℝ (fderiv ℝ (quadraticIdentityMap Q)) 0 (Pi.single d 1) (Pi.single c 1) =
      (fun i => Q i c d) := by
  ext i
  rw [coordinate_vector_second_derivative_component (quadraticIdentityMap Q) 0
    ((quadraticCoordinateMap_smooth 0 (ContinuousLinearEquiv.refl ℝ CoordinatePoint) Q).contDiffAt.of_le
      (by simp)) i c d]
  change scalarPartial (fun x => coordinateJacobian (quadraticCoordinateMap 0
    (ContinuousLinearEquiv.refl ℝ CoordinatePoint) Q) x i c) 0 d = _
  unfold scalarPartial
  rw [(quadraticJacobian_hasFDerivAt _ _ _ symmetric 0 i c).fderiv,
    quadraticJacobianDerivative_basis]

#print axioms coordinate_vector_second_derivative_component
#print axioms quadratic_coordinate_jacobian_second_zero
#print axioms quadratic_identity_vector_second_derivative
end
end AASCSemanticExhaustion
