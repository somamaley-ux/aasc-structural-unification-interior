import WickLorentzSignatureDomain

/-! An actual invertible completion of squares, not a received inertia label. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators Topology Matrix.Norms.Operator
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickTimeMix (G : NativeRealMatrix) : (Fin 3 → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ j,G 0 j.succ*x j
  map_add' x y := by simp [mul_add,Finset.sum_add_distrib]
  map_smul' r x := by simp [mul_left_comm,Finset.mul_sum]

def wickSchurMatrix (G : NativeRealMatrix) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => G i.succ j.succ-G i.succ 0*G 0 j.succ/G 0 0

def wickSchurCoordinates (G : NativeRealMatrix) :
    (Fin 4 → ℝ) ≃ₗ[ℝ] ℝ × (Fin 3 → ℝ) where
  toFun v := (v 0+wickTimeMix G (Fin.tail v)/G 0 0,Fin.tail v)
  invFun v := Fin.cons (v.1-wickTimeMix G v.2/G 0 0) v.2
  left_inv v := by
    dsimp
    simpa only [add_sub_cancel_right] using Fin.cons_self_tail v
  right_inv v := by simp
  map_add' v w := by
    apply Prod.ext
    · change (v 0+w 0)+wickTimeMix G (Fin.tail v+Fin.tail w)/G 0 0=
        (v 0+wickTimeMix G (Fin.tail v)/G 0 0)+(w 0+wickTimeMix G (Fin.tail w)/G 0 0)
      rw [map_add,add_div]
      ring
    · rfl
  map_smul' r v := by
    apply Prod.ext
    · change r*v 0+wickTimeMix G (r • Fin.tail v)/G 0 0=
        r*(v 0+wickTimeMix G (Fin.tail v)/G 0 0)
      rw [map_smul]
      simp only [smul_eq_mul]
      ring
    · rfl

def wickMatrixQuadratic {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i,∑ j,x i*G i j*x j

theorem wick_schur_quadratic_identity (G : NativeRealMatrix)
    (symm : ∀ i j,G i j=G j i) (x : Fin 3 → ℝ) :
    wickMatrixQuadratic (wickSchurMatrix G) x =
      wickMatrixQuadratic (wickSpatialBlock G) x-(wickTimeMix G x)^2/G 0 0 := by
  have cross (i : Fin 3) : G i.succ 0=G 0 i.succ := symm _ _
  simp only [wickMatrixQuadratic,wickSchurMatrix,wickSpatialBlock,wickTimeMix,
    LinearMap.coe_mk,AddHom.coe_mk,mul_sub,sub_mul,Finset.sum_sub_distrib,cross,
    pow_two,Finset.sum_mul,Finset.mul_sum,div_eq_mul_inv]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem wick_schur_coordinates_quadratic (G : NativeRealMatrix)
    (symm : ∀ i j,G i j=G j i) (nonzero : G 0 0≠0) (v : Fin 4 → ℝ) :
    wickMatrixQuadratic G v =
      G 0 0*((wickSchurCoordinates G v).1)^2+
        wickMatrixQuadratic (wickSchurMatrix G) (wickSchurCoordinates G v).2 := by
  rw [wick_schur_quadratic_identity G symm]
  change wickMatrixQuadratic G v =
    G 0 0*(v 0+wickTimeMix G (Fin.tail v)/G 0 0)^2+
      (wickMatrixQuadratic (wickSpatialBlock G) (Fin.tail v)-
        (wickTimeMix G (Fin.tail v))^2/G 0 0)
  have cross (i : Fin 3) : G i.succ 0=G 0 i.succ := symm _ _
  simp only [wickMatrixQuadratic,wickSpatialBlock,wickTimeMix,
    LinearMap.coe_mk,AddHom.coe_mk,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Fin.tail,add_zero]
  simp only [cross]
  field_simp [nonzero]
  <;> ring

theorem wick_schur_positive (G : NativeRealMatrix) (symm : ∀ i j,G i j=G j i)
    (negative : G 0 0<0)
    (spatial : ∀ x : Fin 3 → ℝ,x≠0 → 0<wickMatrixQuadratic (wickSpatialBlock G) x)
    (x : Fin 3 → ℝ) (hx : x≠0) :
    0<wickMatrixQuadratic (wickSchurMatrix G) x := by
  rw [wick_schur_quadratic_identity G symm]
  have nonpos : (wickTimeMix G x)^2/G 0 0≤0 :=
    div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) negative.le
  linarith [spatial x hx]

theorem wick_schur_symmetric (G : NativeRealMatrix) (symm : ∀ i j,G i j=G j i) :
    ∀ i j,wickSchurMatrix G i j=wickSchurMatrix G j i := by
  intro i j
  change G i.succ j.succ-G i.succ 0*G 0 j.succ/G 0 0=
    G j.succ i.succ-G j.succ 0*G 0 i.succ/G 0 0
  rw [symm i.succ j.succ,symm i.succ 0,symm j.succ 0]
  ring

/-- An explicit real linear isomorphism to one negative square and a positive
three-dimensional quadratic block is a signature receipt. -/
def WickLorentzSignature (G : NativeRealMatrix) : Prop :=
  ∃ e : (Fin 4 → ℝ) ≃ₗ[ℝ] ℝ × (Fin 3 → ℝ),
  ∃ A : Matrix (Fin 3) (Fin 3) ℝ,
    G 0 0<0 ∧ (∀ i j,A i j=A j i) ∧
    (∀ x : Fin 3 → ℝ,x≠0 → 0<wickMatrixQuadratic A x) ∧
    ∀ v,wickMatrixQuadratic G v=G 0 0*(e v).1^2+wickMatrixQuadratic A (e v).2

theorem wick_negative_positive_split_is_lorentz (G : NativeRealMatrix)
    (symm : ∀ i j,G i j=G j i) (negative : G 0 0<0)
    (spatial : ∀ x : Fin 3 → ℝ,x≠0 → 0<wickMatrixQuadratic (wickSpatialBlock G) x) :
    WickLorentzSignature G :=
  ⟨wickSchurCoordinates G,wickSchurMatrix G,negative,wick_schur_symmetric G symm,
    wick_schur_positive G symm negative spatial,
    wick_schur_coordinates_quadratic G symm (ne_of_lt negative)⟩

end AASCKleinGordon
