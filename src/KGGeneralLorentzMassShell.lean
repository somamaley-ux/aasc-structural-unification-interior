import KGProperLorentzGroup

/-! The all-matrix action is derived on the original positive-energy mass shell.
No shell-invariance, action law, inverse or Jacobian is received as a field. -/
noncomputable section
set_option maxHeartbeats 1400000
namespace AASCKleinGordon

def spatialFourMomentum (v : FourMomentum) : Momentum := fun j => v j.succ

theorem original_shell_timelike (a : Parameters) (p : Momentum) :
    minkowskiDot (massShell a p) (massShell a p)<0 := by
  rw [massShell_on_shell]
  exact neg_lt_zero.mpr (mul_pos (sq_pos_of_pos a.mass_pos) (sq_pos_of_pos a.speed_pos))

theorem original_shell_future (a : Parameters) (p : Momentum) :
    0<massShell a p 0 := div_pos (energy_pos a p) a.speed_pos

theorem original_shell_unique_forward (a : Parameters) (v : FourMomentum)
    (shell : minkowskiDot v v= -(a.mass^2*a.speed^2)) (future : 0<v 0) :
    massShell a (spatialFourMomentum v)=v := by
  let p:=spatialFourMomentum v
  have hs:=congrArg (fun r : ℝ => a.speed^2*r) shell
  have he:=energy_sq a p
  have hp:=energy_pos a p
  have hc:=a.speed_pos
  have hfuture : 0<a.speed*v 0 := mul_pos hc future
  have heq : energy a p=a.speed*v 0 := by
    dsimp [minkowskiDot] at hs
    dsimp [p,spatialFourMomentum,momentumSq] at he
    nlinarith [hs,he]
  have htime : energy a p/a.speed=v 0 := by
    rw [heq,mul_div_cancel_left₀ _ (ne_of_gt hc)]
  funext j
  fin_cases j
  · exact htime
  · rfl
  · rfl
  · rfl

def lorentzShellMap (a : Parameters) (L : ProperLorentzTransform) (p : Momentum) : Momentum :=
  spatialFourMomentum (L.val (massShell a p))

theorem massShell_lorentzShellMap (a : Parameters) (L : ProperLorentzTransform) (p : Momentum) :
    massShell a (lorentzShellMap a L p)=L.val (massShell a p) := by
  apply original_shell_unique_forward
  · rw [properLorentz_metric,massShell_on_shell]
  · exact properLorentz_future L _ (original_shell_timelike a p) (original_shell_future a p)

theorem energy_lorentzShellMap (a : Parameters) (L : ProperLorentzTransform) (p : Momentum) :
    energy a (lorentzShellMap a L p)/a.speed=L.val (massShell a p) 0 :=
  congrFun (massShell_lorentzShellMap a L p) 0

theorem lorentzShellMap_one (a : Parameters) (p : Momentum) :
    lorentzShellMap a 1 p=p := by
  funext j
  fin_cases j <;> rfl

theorem lorentzShellMap_mul (a : Parameters) (L M : ProperLorentzTransform) (p : Momentum) :
    lorentzShellMap a (L*M) p=lorentzShellMap a L (lorentzShellMap a M p) := by
  change spatialFourMomentum ((L*M).val (massShell a p)) =
    spatialFourMomentum (L.val (massShell a (lorentzShellMap a M p)))
  rw [massShell_lorentzShellMap]
  rfl

theorem lorentzShellMap_inverse_left (a : Parameters) (L : ProperLorentzTransform) (p : Momentum) :
    lorentzShellMap a L⁻¹ (lorentzShellMap a L p)=p := by
  rw [← lorentzShellMap_mul,inv_mul_cancel,lorentzShellMap_one]

theorem lorentzShellMap_inverse_right (a : Parameters) (L : ProperLorentzTransform) (p : Momentum) :
    lorentzShellMap a L (lorentzShellMap a L⁻¹ p)=p := by
  rw [← lorentzShellMap_mul,mul_inv_cancel,lorentzShellMap_one]

def lorentzShellEquiv (a : Parameters) (L : ProperLorentzTransform) : Momentum ≃ Momentum where
  toFun:=lorentzShellMap a L
  invFun:=lorentzShellMap a L⁻¹
  left_inv:=lorentzShellMap_inverse_left a L
  right_inv:=lorentzShellMap_inverse_right a L

theorem lorentzShellMap_bijective (a : Parameters) (L : ProperLorentzTransform) :
    Function.Bijective (lorentzShellMap a L) := (lorentzShellEquiv a L).bijective

theorem lorentzShellMap_injective (a : Parameters) (L : ProperLorentzTransform) :
    Function.Injective (lorentzShellMap a L) := (lorentzShellMap_bijective a L).1

theorem lorentzShellMap_surjective (a : Parameters) (L : ProperLorentzTransform) :
    Function.Surjective (lorentzShellMap a L) := (lorentzShellMap_bijective a L).2

end AASCKleinGordon
