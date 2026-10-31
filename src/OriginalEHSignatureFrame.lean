import OriginalEHLorentzFrameConstruction

namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCKleinGordon
open scoped BigOperators Topology Matrix.Norms.Elementwise

theorem eh_matrix_quadratic_ext (G H : Tensor2)
    (sg : ∀ i j, G i j = G j i) (sh : ∀ i j, H i j = H j i)
    (equal : ∀ v, wickMatrixQuadratic G v = wickMatrixQuadratic H v) : G = H := by
  have diagonal (i : Fin 4) : G i i = H i i := by
    simpa [wickMatrixQuadratic,Pi.single_apply] using equal (Pi.single i 1)
  ext i j
  have sum := equal (Pi.single i 1 + Pi.single j 1)
  simp only [wickMatrixQuadratic,Pi.add_apply,mul_add,add_mul,Finset.sum_add_distrib] at sum
  simp [Pi.single_apply] at sum
  rw [sg j i,sh j i,diagonal i,diagonal j] at sum
  linarith

theorem eh_matrix_quadratic_congruence (G B : Tensor2) (v : CoordinatePoint) :
    wickMatrixQuadratic (B.transpose * G * B) v = wickMatrixQuadratic G (B.mulVec v) := by
  have qdot (M : Tensor2) (x : CoordinatePoint) :
      wickMatrixQuadratic M x = dotProduct x (M.mulVec x) := by
    simp only [wickMatrixQuadratic,dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]
  rw [qdot,qdot]
  simp only [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]

def ehScaledSplitEquiv (c : ℝ) (negative : c < 0)
    (C : Matrix (Fin 3) (Fin 3) ℝ) (unit : IsUnit C.det) :
    (ℝ × (Fin 3 → ℝ)) ≃ₗ[ℝ] CoordinatePoint where
  toFun w := Fin.cons (Real.sqrt (-c) * w.1) (C.mulVec w.2)
  invFun v := (v 0 / Real.sqrt (-c), C⁻¹.mulVec (Fin.tail v))
  left_inv w := by
    have nz : Real.sqrt (-c) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (neg_pos.mpr negative))
    apply Prod.ext
    · simp [nz]
    · simp only [Fin.tail_cons,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul C unit,Matrix.one_mulVec]
  right_inv v := by
    have nz : Real.sqrt (-c) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (neg_pos.mpr negative))
    simp only [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv C unit,Matrix.one_mulVec]
    simpa only [mul_div_cancel₀ _ nz] using Fin.cons_self_tail v
  map_add' w z := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [mul_add]
    · simp [Matrix.mulVec_add]
  map_smul' r w := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Prod.smul_fst,Pi.smul_apply,RingHom.id_apply,smul_eq_mul,Fin.cons_zero]
      ring
    · simp [Matrix.mulVec_smul]

theorem eh_positive_factor_quadratic (C : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    wickMatrixQuadratic (C.transpose * C) x = ∑ i : Fin 3, (C.mulVec x i)^2 := by
  calc
    _ = dotProduct x ((C.transpose * C).mulVec x) := by
      simp only [wickMatrixQuadratic,dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]
    _ = dotProduct (C.mulVec x) (C.mulVec x) := by
      rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]
    _ = _ := by simp only [dotProduct,pow_two]

theorem eh_split_signature_has_frame (G : Tensor2) (sg : ∀ i j, G i j = G j i)
    (signature : WickLorentzSignature G) :
    ∃ B : CoordinatePoint ≃L[ℝ] CoordinatePoint,
      (coordinateFrameMatrix B).transpose * G * coordinateFrameMatrix B = metric := by
  obtain ⟨e,A,negative,symmetric,positive,quadratic⟩ := signature
  let c : ℝ := G 0 0
  obtain ⟨C,unit,factor⟩ := eh_positive_spatial_factor A symmetric positive
  let f := e.trans (ehScaledSplitEquiv c negative C unit)
  let B : CoordinatePoint ≃L[ℝ] CoordinatePoint := f.symm.toContinuousLinearEquiv
  refine ⟨B,?_⟩
  have hB (v : CoordinatePoint) : (coordinateFrameMatrix B).mulVec v = B v := by
    change (LinearMap.toMatrix' B.toLinearEquiv.toLinearMap).mulVec v = B v
    exact LinearMap.toMatrix'_mulVec _ v
  apply eh_matrix_quadratic_ext
  · intro i j
    have symG : G.transpose = G := by ext a b; exact sg b a
    have hs : ((coordinateFrameMatrix B).transpose * G * coordinateFrameMatrix B).transpose =
        (coordinateFrameMatrix B).transpose * G * coordinateFrameMatrix B := by
      simp only [Matrix.transpose_mul,Matrix.transpose_transpose,symG,Matrix.mul_assoc]
    exact congrArg (fun M : Tensor2 => M j i) hs
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro v
    rw [eh_matrix_quadratic_congruence,hB,quadratic]
    have inverse := f.apply_symm_apply v
    have time : Real.sqrt (-c) * (e (B v)).1 = v 0 := congrArg (fun x : CoordinatePoint => x 0) inverse
    have space : C.mulVec (e (B v)).2 = Fin.tail v := congrArg Fin.tail inverse
    have posq : wickMatrixQuadratic A (e (B v)).2 = ∑ i : Fin 3, (v i.succ)^2 := by
      rw [factor,eh_positive_factor_quadratic,space]
      rfl
    rw [posq]
    have sq := Real.sq_sqrt (neg_nonneg.mpr negative.le)
    have timeq : c * (e (B v)).1^2 = -(v 0)^2 := by nlinarith [congrArg (fun x : ℝ => x^2) time]
    rw [timeq]
    simp [wickMatrixQuadratic,metric,Fin.sum_univ_succ,pow_two]

end
end AASCSemanticExhaustion
