import KGNativeWickMetricResponse

/-! An actual common L1 test factor, independent of the particle number.
The finite state-bound below is not asserted continuous in the states. Its
sector-seminorm domination and graph-topology attachment remain separate. -/
noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory TopologicalSpace
open scoped SchwartzMap
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickCoreStressKernelL1 (a : Parameters) (n : ℕ) (u v : FiniteParticleCore)
    (k i j : Fin 4) : ℝ :=
  ∫ z,‖wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n k)
    (wickCoreChannelFrequency1 a n k) (wickCoreChannelStateKernel n u v k) i j z‖
      ∂particleMeasure a (n+2)

theorem wick_core_stress_kernel_L1_nonnegative (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k i j : Fin 4) : 0≤wickCoreStressKernelL1 a n u v k i j :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem wick_core_stress_uniform_L1_bound (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k i j : Fin 4) (x : Spacetime) :
    ‖wickCoreRaisedStressMatrix a n u v k i j x‖≤wickCoreStressKernelL1 a n u v k i j :=
  wickLocalMatrix_uniform_bound a (n+2) _ _ x

def originalWickStressStateBound (a : Parameters) (s : ℝ) (u v : FiniteParticleCore)
    (i j : Fin 4) : ℝ :=
  ‖(s : ℂ)^2‖*∑ k∈(Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4)),
    ‖wickCoreChannelCoefficient k.1 k.2‖*wickCoreStressKernelL1 a k.1 u v k.2 i j

theorem original_wick_stress_state_bound_nonnegative (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (i j : Fin 4) : 0≤originalWickStressStateBound a s u v i j := by
  unfold originalWickStressStateBound
  apply mul_nonneg (norm_nonneg _)
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (norm_nonneg _)
    (wick_core_stress_kernel_L1_nonnegative a k.1 u v k.2 i j))

theorem original_wick_stress_uniform_state_bound (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (i j : Fin 4) (x : Spacetime) :
    ‖originalWickScalarStressRaisedMatrix a s u v i j x‖≤originalWickStressStateBound a s u v i j := by
  rw [original_wick_raised_stress_channel_expansion,norm_mul]
  unfold originalWickStressStateBound
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (wick_core_stress_uniform_L1_bound a k.1 u v k.2 i j x)
    (norm_nonneg _)

theorem original_wick_distribution_common_L1_bound (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (i j : Fin 4) (h : 𝓢(Spacetime,ℂ)) :
    ‖originalWickRaisedStressDistribution a s u v i j h‖≤
      originalWickStressStateBound a s u v i j*(∫ x,‖h x‖) := by
  rw [original_wick_raised_stress_distribution_pairing]
  calc
    _≤∫ x,‖h x*originalWickScalarStressRaisedMatrix a s u v i j x‖ := norm_integral_le_integral_norm _
    _≤∫ x,‖h x‖*originalWickStressStateBound a s u v i j := by
      apply integral_mono (original_wick_raised_stress_test_integrable a s u v i j h).norm
        (h.integrable.norm.mul_const _)
      intro x
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (original_wick_stress_uniform_state_bound a s u v i j x) (norm_nonneg _)
    _=_ := by rw [integral_mul_const];ring

def wickMetricTestL1 (k : WickSchwartzMetricTest) : ℝ := ∑ i,∑ j,∫ x,‖k i j x‖

theorem wick_schwartz_L1_norm (h : 𝓢(Spacetime,ℂ)) :
    ‖h.toLp 1 volume‖=∫ x,‖h x‖ := by
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae ((h.coeFn_toLp 1 volume).fun_comp norm)

theorem wick_metric_test_L1_continuous : Continuous wickMetricTestL1 := by
  unfold wickMetricTestL1
  apply continuous_finset_sum
  intro i hi
  apply continuous_finset_sum
  intro j hj
  have hc : Continuous (fun k : WickSchwartzMetricTest => k i j) :=
    (continuous_apply j).comp (continuous_apply i)
  have hl := (SchwartzMap.toLpCLM ℝ ℂ 1 (volume : Measure Spacetime)).continuous.comp hc
  have hn : Continuous (fun k : WickSchwartzMetricTest => ‖(k i j).toLp 1 volume‖) := hl.norm
  simpa only [wick_schwartz_L1_norm] using hn

theorem native_wick_metric_test_L1_LF_continuous (Ω : Opens (Fin 4 → ℝ)) :
    Continuous (wickMetricTestL1 ∘ nativeToWickMetricTest Ω) :=
  wick_metric_test_L1_continuous.comp (nativeToWickMetricTest Ω).continuous

def originalWickTotalStateBound (a : Parameters) (s : ℝ) (u v : FiniteParticleCore) : ℝ :=
  ∑ i,∑ j,originalWickStressStateBound a s u v i j

theorem original_wick_stress_entry_le_total_state_bound (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (i j : Fin 4) :
    originalWickStressStateBound a s u v i j≤originalWickTotalStateBound a s u v := by
  apply (Finset.single_le_sum (fun l _ => original_wick_stress_state_bound_nonnegative a s u v i l)
    (Finset.mem_univ j)).trans
  exact Finset.single_le_sum (fun m _ => Finset.sum_nonneg (fun l _ =>
    original_wick_stress_state_bound_nonnegative a s u v m l)) (Finset.mem_univ i)

theorem original_wick_metric_distribution_common_L1_bound (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (k : WickSchwartzMetricTest) :
    ‖originalWickStressMetricDistribution a s u v k‖≤
      originalWickTotalStateBound a s u v*wickMetricTestL1 k := by
  simp only [originalWickStressMetricDistribution,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
  apply (norm_sum_le _ _).trans
  calc
    _≤∑ i,∑ j,‖originalWickRaisedStressDistribution a s u v i j (k i j)‖ :=
      Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _≤∑ i,∑ j,originalWickTotalStateBound a s u v*(∫ x,‖k i j x‖) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact (original_wick_distribution_common_L1_bound a s u v i j (k i j)).trans
        (mul_le_mul_of_nonneg_right (original_wick_stress_entry_le_total_state_bound a s u v i j)
          (integral_nonneg (fun _ => norm_nonneg _)))
    _=_ := by simp only [wickMetricTestL1,Finset.mul_sum]

end AASCKleinGordon
