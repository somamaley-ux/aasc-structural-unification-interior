import L2TranslationContinuity
import TranslationScalarDerivative
import L2RealMultiplicationClosed

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AASCKleinGordon.Multiplication
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def orbitSlope (v : X → ℝ) (hv : Measurable v) (hbar t : ℝ) (f : H μ) : H μ :=
  (t⁻¹ : ℝ) • (phaseMultiplier v hv hbar t f-f)

theorem orbitSlope_ae (v : X → ℝ) (hv : Measurable v) (hbar t : ℝ) (f : H μ) :
    orbitSlope v hv hbar t f=ᵐ[μ] (fun x => Translation.phaseSlope hbar t (v x)*f x) := by
  filter_upwards [Lp.coeFn_smul (t⁻¹ : ℝ) (phaseMultiplier v hv hbar t f-f),
    Lp.coeFn_sub (phaseMultiplier v hv hbar t f) f,phaseMultiplier_ae v hv hbar t f] with x h1 h2 h3
  change ((t⁻¹ : ℝ) • (phaseMultiplier v hv hbar t f-f)) x=_
  simp only [Pi.smul_apply,Complex.real_smul] at h1
  simp only [Pi.sub_apply] at h2
  rw [h1,h2,h3]
  simp only [Translation.phaseSlope]
  ring

theorem orbitSlope_norm_bound (v : X → ℝ) (hv : Measurable v) (hbar t : ℝ)
    (f : (realMultiplication (μ:=μ) v).domain) :
    ‖orbitSlope v hv hbar t f.val‖≤‖Translation.coefficient hbar‖*‖realMultiplication v f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [orbitSlope_ae v hv hbar t f.val,realMultiplication_apply_ae v f] with x hx hy
  rw [hx,hy,norm_mul,norm_mul]
  calc
    ‖Translation.phaseSlope hbar t (v x)‖*‖f.val x‖ ≤
        (‖Translation.coefficient hbar‖*‖(v x : ℂ)‖)*‖f.val x‖ :=
      mul_le_mul_of_nonneg_right (Translation.phaseSlope_bound_coefficient hbar t (v x)) (norm_nonneg _)
    _ = ‖Translation.coefficient hbar‖*(‖(v x : ℂ)‖*‖f.val x‖) := mul_assoc _ _ _

theorem phaseMultiplier_hasDerivAt_zero (v : X → ℝ) (hv : Measurable v) (hbar : ℝ)
    (f : (realMultiplication (μ:=μ) v).domain) :
    HasDerivAt (fun t => phaseMultiplier v hv hbar t f.val)
      (Translation.coefficient hbar • realMultiplication v f) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add,phaseMultiplier_zero]
  rw [← tendsto_sub_nhds_zero_iff]
  refine L2_tendsto_zero_of_dominated _
    (fun t x => Translation.phaseSlope hbar t (v x)*f.val x-
      Translation.coefficient hbar*(realMultiplication v f) x)
    ?_ ?_
    (fun x => (2*‖Translation.coefficient hbar‖)*‖(realMultiplication v f) x‖)
    ((Lp.memLp (realMultiplication v f)).norm.const_mul _) ?_ ?_
  · intro t
    filter_upwards [Lp.coeFn_sub (orbitSlope v hv hbar t f.val)
        (Translation.coefficient hbar • realMultiplication v f),
      orbitSlope_ae v hv hbar t f.val,
      Lp.coeFn_smul (Translation.coefficient hbar) (realMultiplication v f)] with x h1 h2 h3
    simp only [Pi.sub_apply] at h1
    simp only [Pi.smul_apply,smul_eq_mul] at h3
    change (orbitSlope v hv hbar t f.val-Translation.coefficient hbar • realMultiplication v f) x=_
    rw [h1,h2,h3]
  · intro t
    have hs : Measurable (fun x => Translation.phaseSlope hbar t (v x)) := by
      unfold Translation.phaseSlope
      exact measurable_const.mul ((translationPhase_measurable v hv hbar t).sub measurable_const)
    exact (hs.aestronglyMeasurable.mul (Lp.memLp f.val).1).sub
      (aestronglyMeasurable_const.mul (Lp.memLp (realMultiplication v f)).1)
  · exact Eventually.of_forall (fun t => (realMultiplication_apply_ae v f).mono (fun x hx => by
      change ‖Translation.phaseSlope hbar t (v x)*f.val x-
          Translation.coefficient hbar*(realMultiplication v f) x‖≤
        (2*‖Translation.coefficient hbar‖)*‖(realMultiplication v f) x‖
      change (realMultiplication v f) x=(v x : ℂ)*f.val x at hx
      rw [hx]
      calc
        ‖Translation.phaseSlope hbar t (v x)*f.val x-
            Translation.coefficient hbar*((v x : ℂ)*f.val x)‖ ≤
            ‖Translation.phaseSlope hbar t (v x)*f.val x‖+
              ‖Translation.coefficient hbar*((v x : ℂ)*f.val x)‖ := norm_sub_le _ _
        _ ≤ (2*‖Translation.coefficient hbar‖)*‖(v x : ℂ)*f.val x‖ := by
          simp only [norm_mul]
          nlinarith [mul_le_mul_of_nonneg_right
            (Translation.phaseSlope_bound_coefficient hbar t (v x)) (norm_nonneg (f.val x))]))
  · exact (realMultiplication_apply_ae v f).mono (fun x hx => by
      have h := ((Translation.phaseSlope_tendsto hbar (v x)).mul_const (f.val x)).sub_const
        (Translation.coefficient hbar*(realMultiplication v f) x)
      simpa only [hx,mul_assoc,sub_self] using h)

end AASCKleinGordon.Multiplication
