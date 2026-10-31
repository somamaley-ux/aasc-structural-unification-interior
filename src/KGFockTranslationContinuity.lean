import KGFockTranslationGroups
import L2TranslationContinuity
import L2HilbertSumConvergence

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open Filter
open scoped Topology
namespace AASCKleinGordon

theorem bosonicPhaseMultiplier_strongly_continuous (a : Parameters) (n : ℕ)
    (v : ParticleConfiguration n → ℝ) (hv : Measurable v)
    (hi : ∀ (σ : Equiv.Perm (Fin n)) x,v (particlePermutation n σ x)=v x)
    (hbar : ℝ) (f : bosonicHilbertSector a n) :
    Continuous (fun t => bosonicPhaseMultiplier a n v hv hi hbar t f) := by
  apply continuous_induced_rng.mpr
  exact Multiplication.phaseMultiplier_strongly_continuous v hv hbar f.val

theorem fockPhaseMultiplier_strongly_continuous (a : Parameters)
    (v : ∀ n,ParticleConfiguration n → ℝ) (hv : ∀ n,Measurable (v n))
    (hi : ∀ n (σ : Equiv.Perm (Fin n)) x,v n (particlePermutation n σ x)=v n x)
    (hbar : ℝ) (f : FockHilbert a) :
    Continuous (fun t => fockPhaseMultiplier a v hv hi hbar t f) := by
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
    have h := (bosonicPhaseMultiplier_strongly_continuous a n (v n) (hv n) (hi n) hbar (f n)).tendsto s
    have hs := h.sub_const (bosonicPhaseMultiplier a n (v n) (hv n) (hi n) hbar s (f n))
    simpa only [sub_self] using hs
  · exact Eventually.of_forall (fun t n => by
      change ‖bosonicPhaseMultiplier a n (v n) (hv n) (hi n) hbar t (f n)-
        bosonicPhaseMultiplier a n (v n) (hv n) (hi n) hbar s (f n)‖≤2*‖f n‖
      calc
        _ ≤ ‖bosonicPhaseMultiplier a n (v n) (hv n) (hi n) hbar t (f n)‖+
            ‖bosonicPhaseMultiplier a n (v n) (hv n) (hi n) hbar s (f n)‖ := norm_sub_le _ _
        _ = 2*‖f n‖ := by rw [bosonicPhaseMultiplier_norm,bosonicPhaseMultiplier_norm,two_mul])

theorem fockSpatialTranslation_strongly_continuous (a : Parameters) (j : Fin 3) (f : FockHilbert a) :
    Continuous (fun t => fockSpatialTranslation a j t f) := fockPhaseMultiplier_strongly_continuous _ _ _ _ _ _

theorem fockTimeTranslation_strongly_continuous (a : Parameters) (f : FockHilbert a) :
    Continuous (fun t => fockTimeTranslation a t f) := fockPhaseMultiplier_strongly_continuous _ _ _ _ _ _

end AASCKleinGordon
