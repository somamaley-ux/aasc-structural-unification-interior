import WickOriginalCoreControls
import WickNativeResponseSesquilinear
import WickJointContinuityCriterion

noncomputable section
set_option maxHeartbeats 8000000
open TopologicalSpace
open scoped SchwartzMap NNReal
open AASCSemanticExhaustion
namespace AASCKleinGordon

lemma wick_metric_test_L1_nonnegative (k : WickSchwartzMetricTest) : 0≤wickMetricTestL1 k := by
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)

def wickNativeResponseLeftSeminorm (a : Parameters) (s : ℝ) : Seminorm ℂ FiniteParticleCore :=
  (1/2 : NNReal) • wickOriginalLeftCoreSeminorm a s

lemma wick_native_response_left_seminorm_continuous (a : Parameters) (s : ℝ) :
    Continuous (wickNativeResponseLeftSeminorm a s) :=
  (wick_original_left_core_seminorm_continuous a s).const_smul (1/2 : ℝ)

theorem original_wick_native_response_continuous_controls_bound (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ)) (H : MetricSourceProbe Ω) :
    ‖originalWickNativeMetricResponse a s u v Ω H‖≤
      wickNativeResponseLeftSeminorm a s u*wickOriginalRightCoreSeminorm a v*
        wickMetricTestL1 (nativeToWickMetricTest Ω H) := by
  apply (original_wick_native_response_common_L1_bound a s u v Ω H).trans
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (original_wick_total_state_bound_continuous_controls a s u v) (by norm_num))
      (wick_metric_test_L1_nonnegative _)).trans_eq
  simp only [wickNativeResponseLeftSeminorm,Seminorm.smul_apply,NNReal.smul_def,
    smul_eq_mul,NNReal.coe_div,NNReal.coe_one]
  have hc : ((2:NNReal):ℝ)=(2:ℝ) := by norm_num
  rw [hc]
  ring

/-- Joint continuity on the ORIGINAL finite-particle core and native LF tests.
The continuous controls were constructed from all actual channel kernels. -/
theorem original_wick_native_response_joint_core_continuous
    (a : Parameters) (s : ℝ) (Ω : Opens (Fin 4 → ℝ)) :
    Continuous (fun z : (FiniteParticleCore × FiniteParticleCore) × MetricSourceProbe Ω =>
      originalWickNativeMetricResponse a s z.1.1 z.1.2 Ω z.2) := by
  apply wick_joint_sesq_test_continuous (originalWickNativeMetricSesq a s Ω)
    (wickNativeResponseLeftSeminorm a s) (wickOriginalRightCoreSeminorm a)
    (fun H => wickMetricTestL1 (nativeToWickMetricTest Ω H))
    (wick_native_response_left_seminorm_continuous a s)
    (wick_original_right_core_seminorm_continuous a)
    (native_wick_metric_test_L1_LF_continuous Ω)
  · simp [wickMetricTestL1]
  · exact fun u v H => original_wick_native_response_continuous_controls_bound a s u v Ω H

end AASCKleinGordon
