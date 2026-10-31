import KGGeneralLorentzDerivative
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

noncomputable section
set_option maxHeartbeats 2200000
namespace AASCKleinGordon

private theorem cons_four_three {α : Type*} (x : α) (v : Fin 3 → α) :
    Fin.cons (α:=fun _ : Fin 4 => α) x v (3 : Fin 4)=v 2 := rfl

private theorem cons_four_two {α : Type*} (x : α) (v : Fin 3 → α) :
    Fin.cons (α:=fun _ : Fin 4 => α) x v (2 : Fin 4)=v 1 := rfl

private theorem cons_four_one {α : Type*} (x : α) (v : Fin 3 → α) :
    Fin.cons (α:=fun _ : Fin 4 => α) x v (1 : Fin 4)=v 0 := rfl

private theorem cons_three_two {α : Type*} (x : α) (v : Fin 2 → α) :
    Fin.cons (α:=fun _ : Fin 3 => α) x v (2 : Fin 3)=v 1 := rfl

private theorem cons_three_one {α : Type*} (x : α) (v : Fin 2 → α) :
    Fin.cons (α:=fun _ : Fin 3 => α) x v (1 : Fin 3)=v 0 := rfl

private theorem cons_two_one {α : Type*} (x : α) (v : Fin 1 → α) :
    Fin.cons (α:=fun _ : Fin 2 => α) x v (1 : Fin 2)=v 0 := rfl

private theorem succAbove_four (j : Fin 4) (i : Fin 3) :
    j.succAbove i=(!![1,2,3;0,2,3;0,1,3;0,1,2] : Matrix (Fin 4) (Fin 3) (Fin 4)) j i := by
  fin_cases j <;> fin_cases i <;> decide

def shellFrameCLM (a : Parameters) (p : Momentum) : FourMomentum →L[ℝ] FourMomentum :=
  (ContinuousLinearMap.proj (0 : Fin 4)).smulRight (massShell a p)+
    (massShellDerivativeCLM a p).comp fourSpatialProjection

def shellFrameMatrix (a : Parameters) (p : Momentum) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![energy a p/a.speed,a.speed*p 0/energy a p,a.speed*p 1/energy a p,a.speed*p 2/energy a p;
     p 0,1,0,0; p 1,0,1,0; p 2,0,0,1]

theorem shellFrameCLM_matrix (a : Parameters) (p : Momentum) :
    LinearMap.toMatrix' (shellFrameCLM a p).toLinearMap=shellFrameMatrix a p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shellFrameCLM,shellFrameMatrix,massShellDerivativeCLM,energyDerivativeCLM,momentumDotCLM,
      LinearMap.toMatrix'_apply,massShell,fourTimeInjection,fourSpatialInjection,
      fourSpatialProjection,fourCoordinateCons,cons_four_three,cons_three_two,
      cons_four_two,cons_four_one,cons_three_one,cons_two_one,
      Fin.tail,Pi.single_apply] <;>
    norm_num <;>
    (try field_simp [a.speed_pos.ne',(energy_pos a p).ne']) <;> ring

theorem shellFrameCLM_det (a : Parameters) (p : Momentum) :
    LinearMap.det (shellFrameCLM a p).toLinearMap=a.mass^2*a.speed^3/energy a p := by
  rw [← LinearMap.det_toMatrix',shellFrameCLM_matrix]
  unfold shellFrameMatrix
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix,
    succAbove_four,Matrix.vecCons,cons_four_three,cons_three_two,
    cons_four_two,cons_four_one,cons_three_one,cons_two_one]
  have he:=energy_sq a p
  dsimp [momentumSq] at he
  field_simp [a.speed_pos.ne',(energy_pos a p).ne']
  nlinarith [he]

def liftedShellDerivative (J : Momentum →L[ℝ] Momentum) : FourMomentum →ₗ[ℝ] FourMomentum :=
  (fourCoordinateCons.toLinearEquiv.toLinearMap.comp
    (LinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) J.toLinearMap)).comp
      fourCoordinateCons.symm.toLinearEquiv.toLinearMap

theorem liftedShellDerivative_det (J : Momentum →L[ℝ] Momentum) :
    LinearMap.det (liftedShellDerivative J)=J.det := by
  calc
    _=LinearMap.det (LinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) J.toLinearMap) :=
      LinearMap.det_conj _ fourCoordinateCons.toLinearEquiv
    _=J.det := by rw [LinearMap.det_prodMap,LinearMap.det_id,one_mul]

theorem liftedShellDerivative_time (J : Momentum →L[ℝ] Momentum) (v : FourMomentum) :
    liftedShellDerivative J v 0=v 0 := rfl

theorem liftedShellDerivative_space (J : Momentum →L[ℝ] Momentum) (v : FourMomentum) :
    fourSpatialProjection (liftedShellDerivative J v)=J (fourSpatialProjection v) := by
  funext i
  fin_cases i <;> rfl

theorem lorentz_shellFrame_intertwines (a : Parameters) (L : ProperLorentzTransform) (p : Momentum) :
    L.val.toLinearMap.comp (shellFrameCLM a p).toLinearMap=
      (shellFrameCLM a (lorentzShellMap a L p)).toLinearMap.comp
        (liftedShellDerivative (lorentzShellDerivativeCLM a L p)) := by
  apply LinearMap.ext
  intro v
  change L.val (v 0 • massShell a p+massShellDerivativeCLM a p (fourSpatialProjection v))=
    (liftedShellDerivative (lorentzShellDerivativeCLM a L p) v) 0 •
        massShell a (lorentzShellMap a L p)+
      massShellDerivativeCLM a (lorentzShellMap a L p)
        (fourSpatialProjection (liftedShellDerivative (lorentzShellDerivativeCLM a L p) v))
  rw [map_add,map_smul,← massShell_lorentzShellMap,liftedShellDerivative_time,liftedShellDerivative_space]
  have hd:=congrArg (fun D : Momentum →L[ℝ] FourMomentum => D (fourSpatialProjection v))
    (lorentzShell_derivative_intertwines a L p)
  exact congrArg (fun w => v 0 • massShell a (lorentzShellMap a L p)+w) hd

theorem lorentzShellDerivative_det (a : Parameters) (L : ProperLorentzTransform) (p : Momentum) :
    (lorentzShellDerivativeCLM a L p).det=energy a (lorentzShellMap a L p)/energy a p := by
  have h:=congrArg LinearMap.det (lorentz_shellFrame_intertwines a L p)
  rw [LinearMap.det_comp,LinearMap.det_comp,properLorentz_det,one_mul,
    shellFrameCLM_det,shellFrameCLM_det,liftedShellDerivative_det] at h
  let K:=a.mass^2*a.speed^3
  have hK : K≠0:=mul_ne_zero (pow_ne_zero _ a.mass_pos.ne') (pow_ne_zero _ a.speed_pos.ne')
  change K/energy a p=K/energy a (lorentzShellMap a L p)*(lorentzShellDerivativeCLM a L p).det at h
  rw [div_mul_eq_mul_div] at h
  have hc:=(div_eq_div_iff (energy_pos a p).ne' (energy_pos a (lorentzShellMap a L p)).ne').mp h
  have hc' : K*energy a (lorentzShellMap a L p)=
      K*((lorentzShellDerivativeCLM a L p).det*energy a p) := by
    simpa only [mul_assoc] using hc
  exact (eq_div_iff (energy_pos a p).ne').mpr (mul_left_cancel₀ hK hc').symm

theorem lorentzShellDerivative_det_pos (a : Parameters) (L : ProperLorentzTransform) (p : Momentum) :
    0<(lorentzShellDerivativeCLM a L p).det := by
  rw [lorentzShellDerivative_det]
  exact div_pos (energy_pos a _) (energy_pos a _)

end AASCKleinGordon
