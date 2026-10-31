import SRScaledBoostHalfTurn

/-! SR 6.4--6.5 group argument after an original spatial comparison aligns
the received rest displacement. The alignment must later be constructed from
the actual full spatial rest family, rather than passed into the final root. -/
namespace AASCMetricConstruction.SRIntegration
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped Matrix

abbrev SRMatrixFrame := ComparisonMatrixˣ

def srIsOriginalProperRestRotation (R : SRMatrixFrame) : Prop :=
  srFramePullback (R : ComparisonMatrix) = comparisonUnitLorentz ∧
    (R : ComparisonMatrix).mulVec (originalComparisonProbe 0) = originalComparisonProbe 0 ∧
    0 < (R : ComparisonMatrix).det

theorem sr_frame_pullback_composition (A B : ComparisonMatrix) :
    srFramePullback (A*B) = B.transpose * srFramePullback A * B := by
  simp [srFramePullback,Matrix.transpose_mul,Matrix.mul_assoc]

theorem sr_scaled_axial_boost_pullback (t r κ a : ℝ)
    (hyperbolic : t^2-r^2=κ) (square : a^2=κ) :
    srFramePullback (srScaledAxialBoost t r a) = κ • comparisonUnitLorentz := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [srFramePullback,srScaledAxialBoost,comparisonUnitLorentz,
      Matrix.transpose_apply,Matrix.mul_apply,Matrix.diagonal,Fin.sum_univ_succ] <;> nlinarith

theorem sr_scaled_axial_boost_determinant (t r a : ℝ) :
    (srScaledAxialBoost t r a).det = (t^2-r^2)*a^2 := by
  norm_num [srScaledAxialBoost,Matrix.det_succ_row_zero,Matrix.det_fin_three,
    Matrix.det_fin_two,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.vecHead,Matrix.vecTail,Fin.succAbove]
  all_goals dsimp [Fin.succ,Fin.instOfNat,Fin.ofNat] at *
  ring

theorem sr_spatial_half_turn_is_original_proper_rest_rotation :
    srIsOriginalProperRestRotation srSpatialHalfTurnUnit := by
  refine ⟨?_,?_,?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [srSpatialHalfTurnUnit,srSpatialHalfTurn,srFramePullback,comparisonUnitLorentz,
        Matrix.mul_apply,Matrix.transpose_apply,Matrix.diagonal,Fin.sum_univ_succ]
  · ext i
    fin_cases i <;> norm_num [srSpatialHalfTurnUnit,srSpatialHalfTurn,originalComparisonProbe,
      Matrix.mulVec,Matrix.diagonal,dotProduct,Fin.sum_univ_succ]
  · norm_num [srSpatialHalfTurnUnit,srSpatialHalfTurn,Matrix.det_diagonal,Fin.prod_univ_succ]

theorem sr_aligned_original_frame_constructs_scaled_boost
    (G : Subgroup SRMatrixFrame) (A S : SRMatrixFrame) (κ t r : ℝ)
    (positive : 0 < κ) (hyperbolic : t^2-r^2=κ)
    (hA : A ∈ G) (hS : S ∈ G)
    (orientedA : 0 < (A : ComparisonMatrix).det)
    (orientedS : 0 < (S : ComparisonMatrix).det)
    (conformalA : srFramePullback (A : ComparisonMatrix) = κ • comparisonUnitLorentz)
    (isometryS : srFramePullback (S : ComparisonMatrix) = comparisonUnitLorentz)
    (aligned : ((S*A : SRMatrixFrame) : ComparisonMatrix).mulVec (originalComparisonProbe 0) =
      ![t,r,0,0])
    (allOriginalRest : ∀ R : SRMatrixFrame, srIsOriginalProperRestRotation R → R ∈ G) :
    srScaledAxialBoostUnit t r κ positive hyperbolic ∈ G := by
  let D := srScaledAxialBoostUnit t r κ positive hyperbolic
  let R := D⁻¹ * S * A
  have factor : D * R = S * A := by dsimp [R];group
  have matrixFactor : (D : ComparisonMatrix) * (R : ComparisonMatrix) =
      (S : ComparisonMatrix) * (A : ComparisonMatrix) := congrArg Units.val factor
  have dform : srFramePullback (D : ComparisonMatrix) = κ • comparisonUnitLorentz :=
    sr_scaled_axial_boost_pullback t r κ (Real.sqrt κ) hyperbolic (Real.sq_sqrt positive.le)
  have rform : srFramePullback (R : ComparisonMatrix) = comparisonUnitLorentz := by
    have h := congrArg srFramePullback matrixFactor
    rw [sr_frame_pullback_composition,sr_frame_pullback_composition,dform,isometryS] at h
    change (R : ComparisonMatrix).transpose * (κ • comparisonUnitLorentz) * (R : ComparisonMatrix) =
      srFramePullback (A : ComparisonMatrix) at h
    rw [conformalA,Matrix.mul_smul,Matrix.smul_mul] at h
    exact (smul_right_injective _ positive.ne') h
  have dcolumn : (D : ComparisonMatrix).mulVec (originalComparisonProbe 0) = ![t,r,0,0] := by
    ext i
    fin_cases i <;> norm_num [D,srScaledAxialBoostUnit,srScaledAxialBoost,
      originalComparisonProbe,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  have rcolumn : (R : ComparisonMatrix).mulVec (originalComparisonProbe 0) = originalComparisonProbe 0 := by
    have h := congrArg (fun M : ComparisonMatrix => M.mulVec (originalComparisonProbe 0)) matrixFactor
    change ((D : ComparisonMatrix)*(R : ComparisonMatrix)).mulVec (originalComparisonProbe 0) =
      ((S*A : SRMatrixFrame) : ComparisonMatrix).mulVec (originalComparisonProbe 0) at h
    rw [← Matrix.mulVec_mulVec,aligned,← dcolumn] at h
    apply_fun (fun v => ((D⁻¹ : SRMatrixFrame) : ComparisonMatrix).mulVec v) at h
    simpa only [Matrix.mulVec_mulVec,← Units.val_mul,← mul_assoc,inv_mul_cancel,
      one_mul,Units.val_one,Matrix.one_mulVec] using h
  have ddet : 0 < (D : ComparisonMatrix).det := by
    change 0 < (srScaledAxialBoost t r (Real.sqrt κ)).det
    rw [sr_scaled_axial_boost_determinant,hyperbolic,Real.sq_sqrt positive.le]
    exact mul_pos positive positive
  have rdet : 0 < (R : ComparisonMatrix).det := by
    have h := congrArg Matrix.det matrixFactor
    rw [Matrix.det_mul,Matrix.det_mul] at h
    have pos : 0 < (D : ComparisonMatrix).det * (R : ComparisonMatrix).det := by
      rw [h]
      exact mul_pos orientedS orientedA
    by_contra hn
    have nonpos := mul_nonpos_of_nonneg_of_nonpos ddet.le (le_of_not_gt hn)
    linarith
  have hr : R ∈ G := allOriginalRest R ⟨rform,rcolumn,rdet⟩
  have result := G.mul_mem (G.mul_mem hS hA) (G.inv_mem hr)
  have same : S*A*R⁻¹ = D := by rw [← factor];group
  rwa [same] at result

#print axioms sr_aligned_original_frame_constructs_scaled_boost
end
end AASCMetricConstruction.SRIntegration
