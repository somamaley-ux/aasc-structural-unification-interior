import KGMassShell
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Algebra.Group.Subgroup.Basic

/-! All proper orthochronous real Lorentz maps on the original four-momentum
carrier. The group is constructed by proving closure of independent metric,
determinant and future conditions. No shell action or Jacobian is an input. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace AASCKleinGordon

def LorentzMetricPreserving (L : FourMomentum ≃ₗ[ℝ] FourMomentum) : Prop :=
  ∀ v w, minkowskiDot (L v) (L w)=minkowskiDot v w

def LorentzFuturePreserving (L : FourMomentum ≃ₗ[ℝ] FourMomentum) : Prop :=
  ∀ v, minkowskiDot v v<0 → 0<v 0 → 0<L v 0

theorem minkowskiDot_neg_neg (v w : FourMomentum) :
    minkowskiDot (-v) (-w)=minkowskiDot v w := by
  simp only [minkowskiDot,Pi.neg_apply]
  ring

theorem timelike_time_ne_zero (v : FourMomentum) (h : minkowskiDot v v<0) : v 0≠0 := by
  intro hz
  simp only [minkowskiDot,hz,zero_mul,neg_zero,zero_add] at h
  nlinarith [sq_nonneg (v 1),sq_nonneg (v 2),sq_nonneg (v 3)]

theorem lorentz_metric_inverse (L : FourMomentum ≃ₗ[ℝ] FourMomentum)
    (h : LorentzMetricPreserving L) : LorentzMetricPreserving L.symm := by
  intro v w
  have hv:=h (L.symm v) (L.symm w)
  simpa only [L.apply_symm_apply] using hv.symm

theorem lorentz_future_inverse (L : FourMomentum ≃ₗ[ℝ] FourMomentum)
    (metric : LorentzMetricPreserving L) (future : LorentzFuturePreserving L) :
    LorentzFuturePreserving L.symm := by
  intro v hv ht
  have hi : minkowskiDot (L.symm v) (L.symm v)<0 := by
    rw [lorentz_metric_inverse L metric]
    exact hv
  rcases lt_or_gt_of_ne (timelike_time_ne_zero (L.symm v) hi) with hn | hp
  · have hneg : 0<(-L.symm v) 0 := by simpa only [Pi.neg_apply] using neg_pos.mpr hn
    have hfuture:=future (-L.symm v) (by rwa [minkowskiDot_neg_neg]) hneg
    simp only [map_neg,L.apply_symm_apply,Pi.neg_apply] at hfuture
    linarith
  · exact hp

theorem lorentz_det_inverse (L : FourMomentum ≃ₗ[ℝ] FourMomentum)
    (proper : LinearMap.det L.toLinearMap=1) : LinearMap.det L.symm.toLinearMap=1 := by
  have hid : L.toLinearMap.comp L.symm.toLinearMap=LinearMap.id := by
    apply LinearMap.ext
    intro v
    exact L.apply_symm_apply v
  have hdet:=congrArg LinearMap.det hid
  rw [LinearMap.det_comp,proper,LinearMap.det_id,one_mul] at hdet
  exact hdet

def properLorentzSubgroup : Subgroup (FourMomentum ≃ₗ[ℝ] FourMomentum) where
  carrier := {L | LorentzMetricPreserving L ∧ LinearMap.det L.toLinearMap=1 ∧
    LorentzFuturePreserving L}
  one_mem' := by
    refine ⟨?_,?_,?_⟩
    · intro v w; rfl
    · exact LinearMap.det_id
    · intro v _ ht; exact ht
  mul_mem' := by
    intro L M hL hM
    refine ⟨?_,?_,?_⟩
    · intro v w
      change minkowskiDot (L (M v)) (L (M w))=minkowskiDot v w
      rw [hL.1,hM.1]
    · change LinearMap.det (L.toLinearMap.comp M.toLinearMap)=1
      rw [LinearMap.det_comp,hL.2.1,hM.2.1,mul_one]
    · intro v hv ht
      change 0<L (M v) 0
      apply hL.2.2 (M v)
      · rwa [hM.1]
      · exact hM.2.2 v hv ht
  inv_mem' := by
    intro L hL
    exact ⟨lorentz_metric_inverse L hL.1,lorentz_det_inverse L hL.2.1,
      lorentz_future_inverse L hL.1 hL.2.2⟩

abbrev ProperLorentzTransform := ↥properLorentzSubgroup

theorem properLorentz_membership_iff (L : FourMomentum ≃ₗ[ℝ] FourMomentum) :
    L∈properLorentzSubgroup ↔ LorentzMetricPreserving L ∧
      LinearMap.det L.toLinearMap=1 ∧ LorentzFuturePreserving L := Iff.rfl

theorem properLorentz_metric (L : ProperLorentzTransform) (v w : FourMomentum) :
    minkowskiDot (L.val v) (L.val w)=minkowskiDot v w := L.property.1 v w

theorem properLorentz_future (L : ProperLorentzTransform) (v : FourMomentum)
    (hv : minkowskiDot v v<0) (ht : 0<v 0) : 0<L.val v 0 := L.property.2.2 v hv ht

theorem properLorentz_det (L : ProperLorentzTransform) : LinearMap.det L.val.toLinearMap=1 :=
  L.property.2.1

theorem properLorentz_one_apply (v : FourMomentum) :
    (1 : ProperLorentzTransform).val v=v := rfl

theorem properLorentz_mul_apply (L M : ProperLorentzTransform) (v : FourMomentum) :
    (L*M).val v=L.val (M.val v) := rfl

theorem properLorentz_inv_apply (L : ProperLorentzTransform) (v : FourMomentum) :
    (L⁻¹).val v=L.val.symm v := rfl

end AASCKleinGordon
