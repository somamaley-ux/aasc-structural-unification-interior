import ActualMetricHessian

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0

theorem scalarPartial_comp (f : CoordinatePoint → ℝ) (F : CoordinatePoint → CoordinatePoint)
    (hf : Differentiable ℝ f) (hF : Differentiable ℝ F) (x : CoordinatePoint) (c : Fin 4) :
    scalarPartial (fun y => f (F y)) x c =
      fderiv ℝ f (F x) (fderiv ℝ F x (Pi.single c 1)) := by
  unfold scalarPartial
  have hd := fderiv_comp x (hf (F x)) (hF x)
  change fderiv ℝ (fun y => f (F y)) x = (fderiv ℝ f (F x)).comp (fderiv ℝ F x) at hd
  rw [hd]
  rfl

theorem scalarFirstJet_comp_zero (f : CoordinatePoint → ℝ) (F : CoordinatePoint → CoordinatePoint)
    (hf : ContDiff ℝ ⊤ f) (hF : ContDiff ℝ ⊤ F)
    (Fzero : F 0 = 0) (first : fderiv ℝ f 0 = 0) :
    fderiv ℝ (fun y => f (F y)) 0 = 0 := by
  have hd := fderiv_comp 0 (hf.differentiable (by simp) (F 0)) (hF.differentiable (by simp) 0)
  change fderiv ℝ (fun y => f (F y)) 0 = (fderiv ℝ f (F 0)).comp (fderiv ℝ F 0) at hd
  simpa only [Fzero, first, ContinuousLinearMap.zero_comp] using hd

theorem scalarSecondJet_comp_identity (f : CoordinatePoint → ℝ) (F : CoordinatePoint → CoordinatePoint)
    (hf : ContDiff ℝ ⊤ f) (hF : ContDiff ℝ ⊤ F)
    (Fzero : F 0 = 0) (DFzero : fderiv ℝ F 0 = ContinuousLinearMap.id ℝ CoordinatePoint)
    (first : fderiv ℝ f 0 = 0) (c d : Fin 4) :
    scalarSecondPartial (fun y => f (F y)) 0 c d = scalarSecondPartial f 0 c d := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) 0 :=
    (hf.contDiffAt.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) 0 :=
    (hF.contDiffAt.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hdfF : DifferentiableAt ℝ (fderiv ℝ f) (F 0) := by simpa only [Fzero] using hdf
  have hA : DifferentiableAt ℝ (fun x => fderiv ℝ f (F x)) 0 :=
    hdfF.comp 0 (hF.differentiable (by simp) 0)
  have hu := hdF.clm_apply (differentiableAt_const (Pi.single c (1 : ℝ)))
  have hpartial : (fun x => scalarPartial (fun y => f (F y)) x c) =
      (fun x => fderiv ℝ f (F x) (fderiv ℝ F x (Pi.single c 1))) :=
    funext (fun x => scalarPartial_comp f F (hf.differentiable (by simp))
      (hF.differentiable (by simp)) x c)
  have hAfderiv : fderiv ℝ (fun x => fderiv ℝ f (F x)) 0 = fderiv ℝ (fderiv ℝ f) 0 := by
    have hd := fderiv_comp 0 hdfF (hF.differentiable (by simp) 0)
    change fderiv ℝ (fun x => fderiv ℝ f (F x)) 0 =
      (fderiv ℝ (fderiv ℝ f) (F 0)).comp (fderiv ℝ F 0) at hd
    simpa only [Fzero, DFzero, ContinuousLinearMap.comp_id] using hd
  unfold scalarSecondPartial
  rw [hpartial]
  unfold scalarPartial
  have hd := fderiv_clm_apply hA hu
  change fderiv ℝ (fun x => fderiv ℝ f (F x) (fderiv ℝ F x (Pi.single c 1))) 0 = _ at hd
  rw [hd]
  simp only [Fzero, first, ContinuousLinearMap.zero_comp, zero_add, hAfderiv, DFzero,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply]
  exact (scalarSecondPartial_full_second_derivative f 0 hf.contDiffAt c d).symm

#print axioms scalarPartial_comp
#print axioms scalarFirstJet_comp_zero
#print axioms scalarSecondJet_comp_identity
end
end AASCSemanticExhaustion
