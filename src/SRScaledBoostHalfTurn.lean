import SRFrameQuadraticRigidity
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! The explicit scaled-boost/half-turn calculation of SR Lemma 6.4.
The arbitrary-frame decomposition into this block and original rest rotations
must be proved separately before using this for the full frame theorem. -/
namespace AASCMetricConstruction.SRIntegration
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped Matrix

def srScaledAxialBoost (t r a : ℝ) : ComparisonMatrix :=
  !![t,r,0,0; r,t,0,0; 0,0,a,0; 0,0,0,a]

def srScaledAxialBoostInverse (t r κ a : ℝ) : ComparisonMatrix :=
  !![t/κ,-r/κ,0,0; -r/κ,t/κ,0,0; 0,0,a⁻¹,0; 0,0,0,a⁻¹]

def srSpatialHalfTurn : ComparisonMatrix := Matrix.diagonal ![1,-1,-1,1]

theorem sr_scaled_axial_boost_inverse_products (t r κ a : ℝ)
    (hκ : κ ≠ 0) (ha : a ≠ 0) (hyperbolic : t^2-r^2=κ) :
    srScaledAxialBoost t r a * srScaledAxialBoostInverse t r κ a = 1 ∧
      srScaledAxialBoostInverse t r κ a * srScaledAxialBoost t r a = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [srScaledAxialBoost,srScaledAxialBoostInverse,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.one_apply] <;>
    field_simp <;> nlinarith

def srScaledAxialBoostUnit (t r κ : ℝ) (positive : 0 < κ) (hyperbolic : t^2-r^2=κ) :
    ComparisonMatrixˣ where
  val := srScaledAxialBoost t r (Real.sqrt κ)
  inv := srScaledAxialBoostInverse t r κ (Real.sqrt κ)
  val_inv := (sr_scaled_axial_boost_inverse_products t r κ (Real.sqrt κ)
    positive.ne' (Real.sqrt_pos.mpr positive).ne' hyperbolic).1
  inv_val := (sr_scaled_axial_boost_inverse_products t r κ (Real.sqrt κ)
    positive.ne' (Real.sqrt_pos.mpr positive).ne' hyperbolic).2

theorem sr_spatial_half_turn_square : srSpatialHalfTurn * srSpatialHalfTurn = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [srSpatialHalfTurn,Matrix.mul_apply,Matrix.diagonal,Fin.sum_univ_succ]

def srSpatialHalfTurnUnit : ComparisonMatrixˣ where
  val := srSpatialHalfTurn
  inv := srSpatialHalfTurn
  val_inv := sr_spatial_half_turn_square
  inv_val := sr_spatial_half_turn_square

def srDilationUnit (κ : ℝ) (nonzero : κ ≠ 0) : ComparisonMatrixˣ where
  val := κ • (1 : ComparisonMatrix)
  inv := κ⁻¹ • (1 : ComparisonMatrix)
  val_inv := by simp [smul_smul,nonzero]
  inv_val := by simp [smul_smul,nonzero]

theorem sr_scaled_axial_boost_half_turn_matrix (t r κ a : ℝ)
    (hyperbolic : t^2-r^2=κ) (square : a^2=κ) :
    srScaledAxialBoost t r a * srSpatialHalfTurn *
      srScaledAxialBoost t r a * srSpatialHalfTurn = κ • (1 : ComparisonMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [srScaledAxialBoost,srSpatialHalfTurn,Matrix.mul_apply,
      Matrix.diagonal,Fin.sum_univ_succ,Matrix.one_apply,Matrix.smul_apply] <;>
    norm_num [Matrix.vecHead,Matrix.vecTail,Pi.smul_apply,smul_eq_mul]
  all_goals dsimp [Fin.succ,Fin.instOfNat,Fin.ofNat,Matrix.vecCons] at *
  all_goals norm_num at *
  all_goals nlinarith

theorem sr_scaled_boost_half_turn_produces_pure_dilation (t r κ : ℝ)
    (positive : 0 < κ) (hyperbolic : t^2-r^2=κ) :
    srScaledAxialBoostUnit t r κ positive hyperbolic * srSpatialHalfTurnUnit *
      srScaledAxialBoostUnit t r κ positive hyperbolic * srSpatialHalfTurnUnit =
        srDilationUnit κ positive.ne' := by
  apply Units.ext
  exact sr_scaled_axial_boost_half_turn_matrix t r κ (Real.sqrt κ) hyperbolic
    (Real.sq_sqrt positive.le)

theorem sr_source_group_contains_scale_dilation
    (G : Subgroup ComparisonMatrixˣ) (t r κ : ℝ) (positive : 0 < κ)
    (hyperbolic : t^2-r^2=κ)
    (boost : srScaledAxialBoostUnit t r κ positive hyperbolic ∈ G)
    (rotation : srSpatialHalfTurnUnit ∈ G) : srDilationUnit κ positive.ne' ∈ G := by
  rw [← sr_scaled_boost_half_turn_produces_pure_dilation t r κ positive hyperbolic]
  exact G.mul_mem (G.mul_mem (G.mul_mem boost rotation) boost) rotation

theorem sr_same_original_rest_tick_eliminates_scaled_boost
    (G : Subgroup ComparisonMatrixˣ) (t r κ T : ℝ) (positive : 0 < κ)
    (tick : 0 < T) (hyperbolic : t^2-r^2=κ)
    (boost : srScaledAxialBoostUnit t r κ positive hyperbolic ∈ G)
    (rotation : srSpatialHalfTurnUnit ∈ G)
    (sameRestTick : ∀ d : ℝ, ∀ hd : 0 < d,
      srDilationUnit d hd.ne' ∈ G → d*T=T) : κ = 1 := by
  have calibration := sameRestTick κ positive
    (sr_source_group_contains_scale_dilation G t r κ positive hyperbolic boost rotation)
  nlinarith

#print axioms sr_scaled_boost_half_turn_produces_pure_dilation
#print axioms sr_same_original_rest_tick_eliminates_scaled_boost
end
end AASCMetricConstruction.SRIntegration
