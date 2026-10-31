import OriginalEHSignatureFrame

namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCKleinGordon Filter Set
open scoped BigOperators Topology Matrix.Norms.Elementwise

def ehFrameNeighborhood (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) : Set Tensor2 :=
  {G | ∀ i j, |((coordinateFrameMatrix B).transpose * G * coordinateFrameMatrix B - metric) i j| < (1:ℝ)/16}

def ehLorentzNeighborhood : Set Tensor2 := ⋃ B : CoordinatePoint ≃L[ℝ] CoordinatePoint, ehFrameNeighborhood B

theorem eh_frame_neighborhood_open (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) :
    IsOpen (ehFrameNeighborhood B) := by
  unfold ehFrameNeighborhood
  simpa only [Set.setOf_forall] using isOpen_iInter_of_finite (fun i : Fin 4 =>
    isOpen_iInter_of_finite (fun j : Fin 4 => isOpen_lt (by fun_prop) continuous_const))

theorem eh_lorentz_neighborhood_open : IsOpen ehLorentzNeighborhood :=
  isOpen_iUnion eh_frame_neighborhood_open

theorem eh_frame_in_lorentz_neighborhood (G : Tensor2)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (frame : (coordinateFrameMatrix B).transpose * G * coordinateFrameMatrix B = metric) :
    G ∈ ehLorentzNeighborhood := by
  apply Set.mem_iUnion.mpr
  refine ⟨B,?_⟩
  intro i j
  rw [frame,sub_self]
  norm_num

theorem eh_coordinate_frame_trans (B D : CoordinatePoint ≃L[ℝ] CoordinatePoint) :
    coordinateFrameMatrix (D.trans B) = coordinateFrameMatrix B * coordinateFrameMatrix D := by
  change LinearMap.toMatrix' (B.toLinearEquiv.toLinearMap.comp D.toLinearEquiv.toLinearMap) = _
  exact LinearMap.toMatrix'_comp _ _

theorem eh_symmetric_lorentz_neighborhood_has_frame (G : Tensor2)
    (symmetric : ∀ i j, G i j = G j i) (inside : G ∈ ehLorentzNeighborhood) :
    ∃ B : CoordinatePoint ≃L[ℝ] CoordinatePoint,
      (coordinateFrameMatrix B).transpose * G * coordinateFrameMatrix B = metric := by
  obtain ⟨B,small⟩ := Set.mem_iUnion.mp inside
  let M := coordinateFrameMatrix B
  let N := M.transpose * G * M
  have sG : G.transpose = G := by ext i j; exact symmetric j i
  have sN : N.transpose = N := by simp [N,Matrix.transpose_mul,sG,Matrix.mul_assoc]
  have symN : ∀ i j, N i j = N j i := fun i j => congrArg (fun A : Tensor2 => A j i) sN
  have negative : N 0 0 < 0 := by
    have h := (abs_lt.mp (small 0 0)).2
    change N 0 0 - metric 0 0 < (1:ℝ)/16 at h
    norm_num [metric] at h
    linarith
  have flat : wickSpatialBlock metric = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have positive (x : Fin 3 → ℝ) (hx : x ≠ 0) :
      0 < wickMatrixQuadratic (wickSpatialBlock N) x := by
    have bound : ∀ i j, |wickSpatialBlock (N-metric) i j| ≤ (1:ℝ)/16 :=
      fun i j => (small i.succ j.succ).le
    have split : wickSpatialBlock N = 1 + wickSpatialBlock (N-metric) := by
      rw [← flat]
      ext i j
      simp [wickSpatialBlock]
    rw [split]
    exact wick_small_spatial_block_pos _ bound x hx
  obtain ⟨D,frame⟩ := eh_split_signature_has_frame N symN
    (wick_negative_positive_split_is_lorentz N symN negative positive)
  refine ⟨D.trans B,?_⟩
  rw [eh_coordinate_frame_trans,Matrix.transpose_mul]
  simpa only [N,M,Matrix.mul_assoc] using frame

end
end AASCSemanticExhaustion
