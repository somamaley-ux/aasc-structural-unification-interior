import EHKGLocalFlatZero

/-! Actual local derivative rules for positive-scale/time-shift coordinate
maps, for later Cauchy continuation on contained dependence diamonds. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

def uniformScaleCLM (scale : ℝ) : CoordinatePoint →L[ℝ] CoordinatePoint :=
  scale • ContinuousLinearMap.id ℝ CoordinatePoint

def timeAffineMap (time scale : ℝ) (p : CoordinatePoint) : CoordinatePoint :=
  time • (Pi.single (0 : Fin 4) (1 : ℝ) : CoordinatePoint) + uniformScaleCLM scale p

theorem time_affine_hasFDerivAt (time scale : ℝ) (p : CoordinatePoint) :
    HasFDerivAt (timeAffineMap time scale) (uniformScaleCLM scale) p := by
  simpa only [zero_add] using (hasFDerivAt_const
    (time • (Pi.single (0 : Fin 4) (1 : ℝ) : CoordinatePoint)) p).add (uniformScaleCLM scale).hasFDerivAt

theorem time_affine_smooth (time scale : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (timeAffineMap time scale) :=
  contDiff_const.add (uniformScaleCLM scale).contDiff

theorem uniform_scale_unit (scale : ℝ) (c : Fin 4) :
    uniformScaleCLM scale (Pi.single c (1 : ℝ)) = scale • (Pi.single c (1 : ℝ) : CoordinatePoint) := rfl

theorem scalar_partial_time_affine (time scale : ℝ) (F : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (regular : DifferentiableAt ℝ F (timeAffineMap time scale p)) (c : Fin 4) :
    scalarPartial (fun x => F (timeAffineMap time scale x)) p c =
      scale * scalarPartial F (timeAffineMap time scale p) c := by
  have first := (regular.hasFDerivAt.comp p (time_affine_hasFDerivAt time scale p)).fderiv
  change fderiv ℝ (fun x => F (timeAffineMap time scale x)) p = _ at first
  rw [scalarPartial, first]
  change fderiv ℝ F (timeAffineMap time scale p) (uniformScaleCLM scale (Pi.single c 1)) = _
  rw [uniform_scale_unit, map_smul]
  rfl

theorem scalar_second_time_affine (time scale : ℝ) (F : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (regular : ContDiffAt ℝ 2 F (timeAffineMap time scale p)) (c d : Fin 4) :
    scalarSecondPartial (fun x => F (timeAffineMap time scale x)) p c d =
      scale ^ 2 * scalarSecondPartial F (timeAffineMap time scale p) c d := by
  have mapRegular : ContDiffAt ℝ 2 (timeAffineMap time scale) p :=
    (time_affine_smooth time scale).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have composed := regular.comp p mapRegular
  change scalarSecondPartial (F ∘ timeAffineMap time scale) p c d = _
  rw [c2_scalarSecondPartial_full_second_derivative _ p composed]
  have nearFirst : ∀ᶠ x in 𝓝 p,
      fderiv ℝ (fun y => F (timeAffineMap time scale y)) x =
        (fderiv ℝ F (timeAffineMap time scale x)).comp (uniformScaleCLM scale) := by
    have nearRegular := (regular.eventually (by simp)).filter_mono
      (time_affine_smooth time scale).continuous.continuousAt
    filter_upwards [nearRegular] with x hx
    change ContDiffAt ℝ 2 F (timeAffineMap time scale x) at hx
    simpa only [Function.comp_def, (time_affine_hasFDerivAt time scale x).fderiv] using
      fderiv_comp x (hx.differentiableAt (by norm_num)) (time_affine_hasFDerivAt time scale x).differentiableAt
  have nearDerivative : (fderiv ℝ (F ∘ timeAffineMap time scale)) =ᶠ[𝓝 p]
      (fun x => (fderiv ℝ F (timeAffineMap time scale x)).comp (uniformScaleCLM scale)) := nearFirst
  rw [nearDerivative.fderiv_eq]
  have secondF := (regular.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have chain := secondF.hasFDerivAt.comp p (time_affine_hasFDerivAt time scale p)
  have second := ((ContinuousLinearMap.compL ℝ CoordinatePoint CoordinatePoint ℝ).flip
    (uniformScaleCLM scale)).hasFDerivAt.comp p chain
  have actual := second.fderiv
  change fderiv ℝ (fun x => (fderiv ℝ F (timeAffineMap time scale x)).comp (uniformScaleCLM scale)) p = _ at actual
  rw [actual]
  change fderiv ℝ (fderiv ℝ F) (timeAffineMap time scale p)
    (uniformScaleCLM scale (Pi.single d 1)) (uniformScaleCLM scale (Pi.single c 1)) = _
  simp only [uniform_scale_unit, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [c2_scalarSecondPartial_full_second_derivative F (timeAffineMap time scale p) regular]
  ring

theorem flat_residual_time_affine (time scale mu : ℝ) (F : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (regular : ContDiffAt ℝ 2 F (timeAffineMap time scale p)) :
    flatScalarResidual ((scale * mu) ^ 2) (fun x => F (timeAffineMap time scale x)) p =
      scale ^ 2 * flatScalarResidual (mu ^ 2) F (timeAffineMap time scale p) := by
  simp only [flatScalarResidual, scalar_second_time_affine time scale F p regular]
  ring

end AASCKleinGordon.CurvedKG
