import EHKGCompactCausalTube
import C2LocalSecondJetCalculus

/-! Local linearity of the actual scalar coordinate derivatives and KG
residual. The hypotheses are C2 at the evaluation point, not global smoothness
or a preselected solution family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

theorem scalar_partial_sub_local (F G : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) (c : Fin 4) :
    scalarPartial (fun x => F x - G x) p c = scalarPartial F p c - scalarPartial G p c := by
  unfold scalarPartial
  have derivative := (hF.hasFDerivAt.sub hG.hasFDerivAt).fderiv
  change fderiv ℝ (fun x => F x - G x) p = _ at derivative
  rw [derivative]
  rfl

theorem scalar_second_partial_sub_local (F G : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (hF : ContDiffAt ℝ 2 F p) (hG : ContDiffAt ℝ 2 G p) (c d : Fin 4) :
    scalarSecondPartial (fun x => F x - G x) p c d = scalarSecondPartial F p c d - scalarSecondPartial G p c d := by
  have near : (fun x => scalarPartial (fun y => F y - G y) x c) =ᶠ[𝓝 p]
      (fun x => scalarPartial F x c - scalarPartial G x c) := by
    filter_upwards [hF.eventually (by norm_num), hG.eventually (by norm_num)] with q hqF hqG
    exact scalar_partial_sub_local F G q (hqF.differentiableAt (by norm_num))
      (hqG.differentiableAt (by norm_num)) c
  change fderiv ℝ (fun x => scalarPartial (fun y => F y - G y) x c) p (Pi.single d 1) = _
  rw [near.fderiv_eq]
  have derivative := ((c2_local_scalarPartial_differentiableAt F p hF c).hasFDerivAt.sub
    (c2_local_scalarPartial_differentiableAt G p hG c).hasFDerivAt).fderiv
  change fderiv ℝ (fun x => scalarPartial F x c - scalarPartial G x c) p = _ at derivative
  rw [derivative]
  rfl

theorem flat_residual_sub_local (mu2 : ℝ) (F G : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (hF : ContDiffAt ℝ 2 F p) (hG : ContDiffAt ℝ 2 G p) :
    flatScalarResidual mu2 (fun x => F x - G x) p =
      flatScalarResidual mu2 F p - flatScalarResidual mu2 G p := by
  simp only [flatScalarResidual, scalar_second_partial_sub_local F G p hF hG]
  ring

end AASCKleinGordon.CurvedKG
