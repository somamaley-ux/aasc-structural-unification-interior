import KGAxisBoostTranslationCompatibility
import KGFockTranslationContinuity

noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory Filter
open scoped Topology
namespace AASCKleinGordon

theorem particleEventPhase_strongly_continuous (a : Parameters) (n : ℕ) (f : ParticleHilbert a n) :
    Continuous (fun b : Spacetime => Multiplication.phaseMultiplier (particleEventMomentum a n b)
      (particleEventMomentum_continuous a n b).measurable a.hbar 1 f) := by
  have hc (x : ParticleConfiguration n) : Continuous (fun b : Spacetime =>
      Translation.phase a.hbar 1 (particleEventMomentum a n b x)) := by
    unfold Translation.phase particleEventMomentum eventMomentumPair
    fun_prop
  apply continuous_iff_continuousAt.mpr
  intro s
  rw [ContinuousAt,← tendsto_sub_nhds_zero_iff]
  refine Multiplication.L2_tendsto_zero_of_dominated _
    (fun b x => (Translation.phase a.hbar 1 (particleEventMomentum a n b x)-
      Translation.phase a.hbar 1 (particleEventMomentum a n s x))*f x) ?_ ?_
    (fun x => 2*‖f x‖) ((Lp.memLp f).norm.const_mul 2) ?_ ?_
  · intro b
    filter_upwards [Lp.coeFn_sub
      (Multiplication.phaseMultiplier (particleEventMomentum a n b) (particleEventMomentum_continuous a n b).measurable a.hbar 1 f)
      (Multiplication.phaseMultiplier (particleEventMomentum a n s) (particleEventMomentum_continuous a n s).measurable a.hbar 1 f),
      Multiplication.phaseMultiplier_ae (particleEventMomentum a n b) (particleEventMomentum_continuous a n b).measurable a.hbar 1 f,
      Multiplication.phaseMultiplier_ae (particleEventMomentum a n s) (particleEventMomentum_continuous a n s).measurable a.hbar 1 f] with x h1 h2 h3
    simp only [Pi.sub_apply] at h1
    change (Multiplication.phaseMultiplier (particleEventMomentum a n b) (particleEventMomentum_continuous a n b).measurable a.hbar 1 f-
      Multiplication.phaseMultiplier (particleEventMomentum a n s) (particleEventMomentum_continuous a n s).measurable a.hbar 1 f) x=_
    rw [h1,h2,h3,sub_mul]
  · intro b
    exact ((Multiplication.translationPhase_measurable (particleEventMomentum a n b) (particleEventMomentum_continuous a n b).measurable a.hbar 1).aestronglyMeasurable.sub
      (Multiplication.translationPhase_measurable (particleEventMomentum a n s) (particleEventMomentum_continuous a n s).measurable a.hbar 1).aestronglyMeasurable).mul (Lp.memLp f).1
  · exact Eventually.of_forall (fun b => Eventually.of_forall (fun x => by
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      calc
        _ ≤ ‖Translation.phase a.hbar 1 (particleEventMomentum a n b x)‖+
          ‖Translation.phase a.hbar 1 (particleEventMomentum a n s x)‖ := norm_sub_le _ _
        _ = 2 := by simp only [Translation.phase_norm]; norm_num))
  · exact Eventually.of_forall (fun x => by
      have h := (((hc x).tendsto s).sub_const
        (Translation.phase a.hbar 1 (particleEventMomentum a n s x))).mul_const (f x)
      simpa only [sub_self,zero_mul] using h)

theorem bosonicEventPhase_strongly_continuous (a : Parameters) (n : ℕ) (f : bosonicHilbertSector a n) :
    Continuous (fun b : Spacetime => bosonicPhaseMultiplier a n (particleEventMomentum a n b)
      (particleEventMomentum_continuous a n b).measurable (particleEventMomentum_permutation a n b) a.hbar 1 f) := by
  apply continuous_induced_rng.mpr
  exact particleEventPhase_strongly_continuous a n f.val

theorem fockEventTranslation_strongly_continuous (a : Parameters) (f : FockHilbert a) :
    Continuous (fun b : Spacetime => fockEventTranslation a b f) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  rw [ContinuousAt,← tendsto_sub_nhds_zero_iff]
  apply HilbertSum.tendsto_zero_of_dominated _ (fun n => 2*‖f n‖) ?_ ?_ ?_
  · have h := ((lp.memℓp f).summable (by norm_num)).mul_left 4
    convert h using 1
    funext n
    simp only [ENNReal.toReal_ofNat,Real.rpow_two,mul_pow]
    ring
  · intro n
    have h := (bosonicEventPhase_strongly_continuous a n (f n)).tendsto s
    have hs := h.sub_const (bosonicPhaseMultiplier a n (particleEventMomentum a n s)
      (particleEventMomentum_continuous a n s).measurable (particleEventMomentum_permutation a n s) a.hbar 1 (f n))
    simpa only [sub_self] using hs
  · exact Eventually.of_forall (fun b n => by
      change ‖bosonicPhaseMultiplier a n (particleEventMomentum a n b) (particleEventMomentum_continuous a n b).measurable (particleEventMomentum_permutation a n b) a.hbar 1 (f n)-
        bosonicPhaseMultiplier a n (particleEventMomentum a n s) (particleEventMomentum_continuous a n s).measurable (particleEventMomentum_permutation a n s) a.hbar 1 (f n)‖≤2*‖f n‖
      calc
        _ ≤ ‖bosonicPhaseMultiplier a n (particleEventMomentum a n b) (particleEventMomentum_continuous a n b).measurable (particleEventMomentum_permutation a n b) a.hbar 1 (f n)‖+
          ‖bosonicPhaseMultiplier a n (particleEventMomentum a n s) (particleEventMomentum_continuous a n s).measurable (particleEventMomentum_permutation a n s) a.hbar 1 (f n)‖ := norm_sub_le _ _
        _ = 2*‖f n‖ := by rw [bosonicPhaseMultiplier_norm,bosonicPhaseMultiplier_norm,two_mul])

end AASCKleinGordon
