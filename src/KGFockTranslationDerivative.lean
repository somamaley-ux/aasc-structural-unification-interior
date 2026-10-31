import KGBosonicTranslationDerivative
import L2HilbertSumConvergence
import KGFockMaximalMultiplication

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
open scoped Topology
namespace AASCKleinGordon

theorem fockPhase_hasDerivAt_zero (a : Parameters)
    (v : ∀ n,ParticleConfiguration n → ℝ) (hv : ∀ n,Measurable (v n))
    (hi : ∀ n (σ : Equiv.Perm (Fin n)) x,v n (particlePermutation n σ x)=v n x)
    (hbar : ℝ) (f : (fockRealMultiplication a v hv hi).domain) :
    HasDerivAt (fun t => fockPhaseMultiplier a v hv hi hbar t f.val)
      (Translation.coefficient hbar • fockRealMultiplication a v hv hi f) 0 := by
  let g := fockRealMultiplication a v hv hi f
  have hg : ∀ n,(g n).val=ᵐ[particleMeasure a n] (fun x => (v n x : ℂ)*(f.val n).val x) :=
    (fockRealMultiplication_mem_graph a v hv hi f.val g).1
      ((fockRealMultiplication a v hv hi).mem_graph f)
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add,fockPhaseMultiplier_zero]
  rw [← tendsto_sub_nhds_zero_iff]
  refine HilbertSum.tendsto_zero_of_dominated _ (fun n => (2*‖Translation.coefficient hbar‖)*‖g n‖) ?_ ?_ ?_
  · have h := ((lp.memℓp g).summable (by norm_num)).mul_left ((2*‖Translation.coefficient hbar‖)^2)
    convert h using 1
    funext n
    simp only [ENNReal.toReal_ofNat,Real.rpow_two,mul_pow]
  · intro n
    have h := (bosonicPhase_hasDerivAt_zero_of_graph a n (v n) (hv n) (hi n) hbar
      (f.val n) (g n) (hg n)).tendsto_slope_zero
    have h' := h.sub_const (Translation.coefficient hbar • g n)
    simpa only [zero_add,bosonicPhaseMultiplier_zero,sub_self] using h'
  · exact Eventually.of_forall (fun t n => by
      change ‖(t⁻¹ : ℝ) • (bosonicPhaseMultiplier a n (v n) (hv n) (hi n) hbar t (f.val n)-f.val n)-
        Translation.coefficient hbar • g n‖≤(2*‖Translation.coefficient hbar‖)*‖g n‖
      have hb := bosonicPhase_slope_bound_of_graph a n (v n) (hv n) (hi n) hbar t
        (f.val n) (g n) (hg n)
      calc
        _ ≤ ‖(t⁻¹ : ℝ) • (bosonicPhaseMultiplier a n (v n) (hv n) (hi n) hbar t (f.val n)-f.val n)‖+
            ‖Translation.coefficient hbar • g n‖ := norm_sub_le _ _
        _ ≤ (2*‖Translation.coefficient hbar‖)*‖g n‖ := by
          simp only [norm_smul] at hb ⊢
          nlinarith)

end AASCKleinGordon
