import L2TranslationPhase
import L2DominatedConvergence

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AASCKleinGordon.Translation

theorem phase_continuous (hbar r : ℝ) : Continuous (fun t => phase hbar t r) := by
  unfold phase
  fun_prop

end AASCKleinGordon.Translation

namespace AASCKleinGordon.Multiplication
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem phaseMultiplier_strongly_continuous (v : X → ℝ) (hv : Measurable v)
    (hbar : ℝ) (f : H μ) : Continuous (fun t => phaseMultiplier v hv hbar t f) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  rw [ContinuousAt,← tendsto_sub_nhds_zero_iff]
  refine L2_tendsto_zero_of_dominated _
    (fun t x => (Translation.phase hbar t (v x)-Translation.phase hbar s (v x))*f x)
    ?_
    (fun t => ((translationPhase_measurable v hv hbar t).aestronglyMeasurable.sub
      (translationPhase_measurable v hv hbar s).aestronglyMeasurable).mul (Lp.memLp f).1)
    (fun x => 2*‖f x‖) ((Lp.memLp f).norm.const_mul 2) ?_ ?_
  · intro t
    filter_upwards [Lp.coeFn_sub (phaseMultiplier v hv hbar t f) (phaseMultiplier v hv hbar s f),
      phaseMultiplier_ae v hv hbar t f,phaseMultiplier_ae v hv hbar s f] with x h1 h2 h3
    simp only [Pi.sub_apply] at h1
    change (phaseMultiplier v hv hbar t f-phaseMultiplier v hv hbar s f) x=_
    rw [h1,h2,h3,sub_mul]
  · exact Eventually.of_forall (fun t => Eventually.of_forall (fun x => by
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      calc
        ‖Translation.phase hbar t (v x)-Translation.phase hbar s (v x)‖ ≤
            ‖Translation.phase hbar t (v x)‖+‖Translation.phase hbar s (v x)‖ := norm_sub_le _ _
        _ = 2 := by simp only [Translation.phase_norm]; norm_num))
  · exact Eventually.of_forall (fun x => by
      have hc : Tendsto (fun t => Translation.phase hbar t (v x)) (𝓝 s)
          (𝓝 (Translation.phase hbar s (v x))) := (Translation.phase_continuous hbar (v x)).tendsto s
      have h := (hc.sub_const (Translation.phase hbar s (v x))).mul_const (f x)
      simpa only [sub_self,zero_mul] using h)

end AASCKleinGordon.Multiplication
