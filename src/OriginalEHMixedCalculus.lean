import OriginalEHInverseMixedVariation
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Actual mixed differentiation on the parameter/coordinate product.
The comparison is proved from symmetry of the genuine second derivative. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Filter
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise

abbrev EHJointPoint := ℝ × CoordinatePoint

theorem eh_joint_space_partial (F : EHJointPoint → ℝ) (t : ℝ) (p : CoordinatePoint)
    (hd : DifferentiableAt ℝ F (t,p)) (c : Fin 4) :
    scalarPartial (fun x => F (t,x)) p c =
      fderiv ℝ F (t,p) (0,Pi.single c 1) := by
  have hp := (hasFDerivAt_const (𝕜 := ℝ) t p).prodMk (hasFDerivAt_id p)
  have hf := (hd.hasFDerivAt.comp p hp).fderiv
  change fderiv ℝ (fun x => F (t,x)) p = _ at hf
  simp only [scalarPartial,hf,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.id_apply]

theorem eh_joint_time_deriv (F : EHJointPoint → ℝ) (t : ℝ) (p : CoordinatePoint)
    (hd : DifferentiableAt ℝ F (t,p)) :
    deriv (fun s => F (s,p)) t = fderiv ℝ F (t,p) (1,0) := by
  have hp := (hasDerivAt_id t).prodMk (hasDerivAt_const t p)
  exact (hd.hasFDerivAt.comp_hasDerivAt t hp).deriv

theorem eh_joint_directional_hasFDerivAt (F : EHJointPoint → ℝ) (z v : EHJointPoint)
    (hf : ContDiffAt ℝ 2 F z) :
    HasFDerivAt (fun y => fderiv ℝ F y v)
      ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ F) z)) z := by
  have hd := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.clm_apply (hasFDerivAt_const (𝕜 := ℝ) v z)
  have he : ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ F) z)) =
      (fderiv ℝ F z).comp (0 : EHJointPoint →L[ℝ] EHJointPoint) +
        (fderiv ℝ (fderiv ℝ F) z).flip v := by
    apply ContinuousLinearMap.ext
    intro w
    change fderiv ℝ (fderiv ℝ F) z w v =
      fderiv ℝ F z 0 + fderiv ℝ (fderiv ℝ F) z w v
    simp only [map_zero,zero_add]
  rw [he]
  exact hd

theorem eh_actual_mixed_partial (F : EHJointPoint → ℝ) (Z : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (hf : ContDiffAt ℝ 2 F (0,p))
    (hz : Z =ᶠ[𝓝 p] fun q => deriv (fun t => F (t,q)) 0) (c : Fin 4) :
    HasDerivAt (fun t => scalarPartial (fun x => F (t,x)) p c)
      (scalarPartial Z p c) 0 := by
  have near : ∀ᶠ z in 𝓝 (0,p), DifferentiableAt ℝ F z :=
    (hf.eventually (by norm_num)).mono
      (fun _ h => h.differentiableAt (by norm_num))
  have hp := (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) p).prodMk (hasFDerivAt_id p)
  have ht := (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) p)
  have zn : Z =ᶠ[𝓝 p] fun q => fderiv ℝ F (0,q) (1,0) := by
    filter_upwards [hz,hp.continuousAt.tendsto.eventually near] with q hq hdiff
    exact hq.trans (eh_joint_time_deriv F 0 q hdiff)
  have hspace := (eh_joint_directional_hasFDerivAt F (0,p) (1,0) hf).comp p hp
  have spaceValue : scalarPartial Z p c =
      fderiv ℝ (fderiv ℝ F) (0,p) (0,Pi.single c 1) (1,0) := by
    unfold scalarPartial
    have hs := hspace.fderiv
    change fderiv ℝ (fun q => fderiv ℝ F (0,q) (1,0)) p = _ at hs
    rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) zn,hs]
    rfl
  have htime := (eh_joint_directional_hasFDerivAt F (0,p) (0,Pi.single c 1) hf).comp_hasDerivAt 0 ht
  have hsame : (fun t => scalarPartial (fun x => F (t,x)) p c) =ᶠ[𝓝 0]
      fun t => fderiv ℝ F (t,p) (0,Pi.single c 1) := by
    filter_upwards [ht.continuousAt.tendsto.eventually near] with t hdiff
    exact eh_joint_space_partial F t p hdiff c
  rw [spaceValue,(hf.isSymmSndFDerivAt (by norm_num)).eq (0,Pi.single c 1) (1,0)]
  exact htime.congr_of_eventuallyEq hsame

end
end AASCSemanticExhaustion
