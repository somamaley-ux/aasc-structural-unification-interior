import WickStressSectorControls
import WickCoreSeminormSums

noncomputable section
set_option maxHeartbeats 8000000
open scoped SchwartzMap NNReal
namespace AASCKleinGordon

/-- A proved control of one actual channel; populated by the constructor below. -/
structure WickSectorPairControl (n r t : ℕ) (B : FiniteParticleCore → FiniteParticleCore → ℝ) where
  left : Seminorm ℂ 𝓢(ParticleConfiguration (n+r),ℂ)
  right : Seminorm ℂ 𝓢(ParticleConfiguration (n+t),ℂ)
  left_continuous : Continuous left
  right_continuous : Continuous right
  bound : ∀ u v,B u v≤left (u (n+r)).val*right (v (n+t)).val

structure WickOriginalChannelControls (a : Parameters) (n : ℕ) where
  cc : WickSectorPairControl n 2 0 (fun u v =>
    wickChannelKernelL1Seminorm a n 0 (wickCoreChannelStateKernel n u v 0))
  mixed1 : WickSectorPairControl n 1 1 (fun u v =>
    wickChannelKernelL1Seminorm a n 1 (wickCoreChannelStateKernel n u v 1))
  mixed2 : WickSectorPairControl n 1 1 (fun u v =>
    wickChannelKernelL1Seminorm a n 2 (wickCoreChannelStateKernel n u v 2))
  aa : WickSectorPairControl n 0 2 (fun u v =>
    wickChannelKernelL1Seminorm a n 3 (wickCoreChannelStateKernel n u v 3))

theorem wick_original_channel_controls_exist (a : Parameters) (n : ℕ) :
    Nonempty (WickOriginalChannelControls a n) := by
  obtain ⟨p0,q0,hp0,hq0,hb0⟩ := wick_aa_continuous_seminorm_control n
    ((wickChannelKernelL1Seminorm a n 0).comp wickSchwartzConjugateSLM)
    (wick_seminorm_conjugate_continuous _ (wick_channel_kernel_L1_seminorm_continuous a n 0))
  obtain ⟨p1,q1,hp1,hq1,hb1⟩ := wick_mixed_continuous_seminorm_control n
    (wickChannelKernelL1Seminorm a n 1) (wick_channel_kernel_L1_seminorm_continuous a n 1)
  obtain ⟨p2,q2,hp2,hq2,hb2⟩ := wick_mixed_continuous_seminorm_control n
    (wickChannelKernelL1Seminorm a n 2) (wick_channel_kernel_L1_seminorm_continuous a n 2)
  obtain ⟨p3,q3,hp3,hq3,hb3⟩ := wick_aa_continuous_seminorm_control n
    (wickChannelKernelL1Seminorm a n 3) (wick_channel_kernel_L1_seminorm_continuous a n 3)
  refine ⟨⟨⟨q0,p0,hq0,hp0,?_⟩,⟨p1,q1,hp1,hq1,?_⟩,
    ⟨p2,q2,hp2,hq2,?_⟩,⟨p3,q3,hp3,hq3,?_⟩⟩⟩
  · intro u v
    simpa [wickCoreChannelStateKernel,Seminorm.comp_apply,wickSchwartzConjugateSLM,mul_comm] using hb0 (v n).val (u (n+2)).val
  · intro u v
    exact hb1 (u (n+1)).val (v (n+1)).val
  · intro u v
    exact hb2 (u (n+1)).val (v (n+1)).val
  · intro u v
    exact hb3 (u n).val (v (n+2)).val

def wickOriginalChannelControls (a : Parameters) (n : ℕ) : WickOriginalChannelControls a n :=
  Classical.choice (wick_original_channel_controls_exist a n)

def wickLeftChannelCoreSeminorm (a : Parameters) (k : Fin 4) : Seminorm ℂ FiniteParticleCore :=
  ![wickCoreShiftSeminorm 2 (fun n => (wickOriginalChannelControls a n).cc.left),
    wickCoreShiftSeminorm 1 (fun n => (wickOriginalChannelControls a n).mixed1.left),
    wickCoreShiftSeminorm 1 (fun n => (wickOriginalChannelControls a n).mixed2.left),
    wickCoreShiftSeminorm 0 (fun n => (wickOriginalChannelControls a n).aa.left)] k

def wickRightChannelCoreSeminorm (a : Parameters) (k : Fin 4) : Seminorm ℂ FiniteParticleCore :=
  ![wickCoreShiftSeminorm 0 (fun n => (wickOriginalChannelControls a n).cc.right),
    wickCoreShiftSeminorm 1 (fun n => (wickOriginalChannelControls a n).mixed1.right),
    wickCoreShiftSeminorm 1 (fun n => (wickOriginalChannelControls a n).mixed2.right),
    wickCoreShiftSeminorm 2 (fun n => (wickOriginalChannelControls a n).aa.right)] k

lemma wick_left_channel_core_seminorm_continuous (a : Parameters) (k : Fin 4) :
    Continuous (wickLeftChannelCoreSeminorm a k) := by
  fin_cases k
  · exact wick_core_shift_seminorm_continuous 2 _ (fun n => (wickOriginalChannelControls a n).cc.left_continuous)
  · exact wick_core_shift_seminorm_continuous 1 _ (fun n => (wickOriginalChannelControls a n).mixed1.left_continuous)
  · exact wick_core_shift_seminorm_continuous 1 _ (fun n => (wickOriginalChannelControls a n).mixed2.left_continuous)
  · exact wick_core_shift_seminorm_continuous 0 _ (fun n => (wickOriginalChannelControls a n).aa.left_continuous)

lemma wick_right_channel_core_seminorm_continuous (a : Parameters) (k : Fin 4) :
    Continuous (wickRightChannelCoreSeminorm a k) := by
  fin_cases k
  · exact wick_core_shift_seminorm_continuous 0 _ (fun n => (wickOriginalChannelControls a n).cc.right_continuous)
  · exact wick_core_shift_seminorm_continuous 1 _ (fun n => (wickOriginalChannelControls a n).mixed1.right_continuous)
  · exact wick_core_shift_seminorm_continuous 1 _ (fun n => (wickOriginalChannelControls a n).mixed2.right_continuous)
  · exact wick_core_shift_seminorm_continuous 2 _ (fun n => (wickOriginalChannelControls a n).aa.right_continuous)

lemma wick_actual_channel_finite_sum_bound (a : Parameters) (k : Fin 4)
    (u v : FiniteParticleCore) (S : Finset ℕ) :
    (∑ n ∈ S,wickChannelKernelL1Seminorm a n k (wickCoreChannelStateKernel n u v k))≤
      wickLeftChannelCoreSeminorm a k u*wickRightChannelCoreSeminorm a k v := by
  fin_cases k
  · apply (Finset.sum_le_sum (fun n _ => (wickOriginalChannelControls a n).cc.bound u v)).trans
    exact wick_core_shift_product_bound 2 0 _ _ u v S
  · apply (Finset.sum_le_sum (fun n _ => (wickOriginalChannelControls a n).mixed1.bound u v)).trans
    exact wick_core_shift_product_bound 1 1 _ _ u v S
  · apply (Finset.sum_le_sum (fun n _ => (wickOriginalChannelControls a n).mixed2.bound u v)).trans
    exact wick_core_shift_product_bound 1 1 _ _ u v S
  · apply (Finset.sum_le_sum (fun n _ => (wickOriginalChannelControls a n).aa.bound u v)).trans
    exact wick_core_shift_product_bound 0 2 _ _ u v S

def wickAmplitudeNormSquared (s : ℝ) : NNReal := ⟨‖(s:ℂ)^2‖,norm_nonneg _⟩

def wickOriginalLeftCoreSeminorm (a : Parameters) (s : ℝ) : Seminorm ℂ FiniteParticleCore :=
  wickAmplitudeNormSquared s • ∑ k : Fin 4,wickLeftChannelCoreSeminorm a k

def wickOriginalRightCoreSeminorm (a : Parameters) : Seminorm ℂ FiniteParticleCore :=
  ∑ k : Fin 4,wickRightChannelCoreSeminorm a k

lemma wick_original_left_core_seminorm_continuous (a : Parameters) (s : ℝ) :
    Continuous (wickOriginalLeftCoreSeminorm a s) := by
  change Continuous (fun u => wickOriginalLeftCoreSeminorm a s u)
  simpa only [wickOriginalLeftCoreSeminorm,Seminorm.smul_apply,wick_seminorm_sum_apply,
    NNReal.smul_def,smul_eq_mul,wickAmplitudeNormSquared,NNReal.coe_mk] using
      (continuous_finset_sum Finset.univ (fun k _ => wick_left_channel_core_seminorm_continuous a k)).const_smul ‖(s:ℂ)^2‖

lemma wick_original_right_core_seminorm_continuous (a : Parameters) :
    Continuous (wickOriginalRightCoreSeminorm a) := by
  change Continuous (fun v => wickOriginalRightCoreSeminorm a v)
  simpa only [wickOriginalRightCoreSeminorm,wick_seminorm_sum_apply] using
    continuous_finset_sum Finset.univ (fun k _ => wick_right_channel_core_seminorm_continuous a k)

lemma wick_four_sum_exchange {α β γ δ : Type*} (A : Finset α) (B : Finset β)
    (C : Finset γ) (D : Finset δ) (f : α → β → γ → δ → ℝ) :
    (∑ a ∈ A,∑ b ∈ B,∑ c ∈ C,∑ d ∈ D,f a b c d)=
      ∑ c ∈ C,∑ d ∈ D,∑ a ∈ A,∑ b ∈ B,f a b c d := by
  calc
    _ = ∑ a ∈ A,∑ c ∈ C,∑ b ∈ B,∑ d ∈ D,f a b c d := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ c ∈ C,∑ a ∈ A,∑ b ∈ B,∑ d ∈ D,f a b c d := Finset.sum_comm
    _ = ∑ c ∈ C,∑ a ∈ A,∑ d ∈ D,∑ b ∈ B,f a b c d := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      exact Finset.sum_comm

lemma original_wick_total_state_bound_channel_sum (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) :
    originalWickTotalStateBound a s u v=‖(s:ℂ)^2‖*
      ∑ n ∈ Finset.range (wickJointCoreCutoff u v),∑ k : Fin 4,
        wickChannelKernelL1Seminorm a n k (wickCoreChannelStateKernel n u v k) := by
  have hproduct (i j : Fin 4) :
      (∑ k ∈ (Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4)),
        ‖wickCoreChannelCoefficient k.1 k.2‖*wickCoreStressKernelL1 a k.1 u v k.2 i j)=
      ∑ n ∈ Finset.range (wickJointCoreCutoff u v),∑ k : Fin 4,
        ‖wickCoreChannelCoefficient n k‖*wickCoreStressKernelL1 a n u v k i j :=
    Finset.sum_product _ _ _
  simp only [originalWickTotalStateBound,originalWickStressStateBound]
  simp_rw [hproduct]
  simpa only [wick_channel_kernel_L1_seminorm_original,Finset.mul_sum,mul_assoc] using
    wick_four_sum_exchange (Finset.univ : Finset (Fin 4)) Finset.univ
      (Finset.range (wickJointCoreCutoff u v)) Finset.univ
      (fun i j n k => ‖(s:ℂ)^2‖*(‖wickCoreChannelCoefficient n k‖*wickCoreStressKernelL1 a n u v k i j))

/-- Continuous original-core controls dominate the entire actual cutoff bound;
no continuity of the cutoff or finite state bound is assumed. -/
theorem original_wick_total_state_bound_continuous_controls (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) :
    originalWickTotalStateBound a s u v≤
      wickOriginalLeftCoreSeminorm a s u*wickOriginalRightCoreSeminorm a v := by
  rw [original_wick_total_state_bound_channel_sum]
  have he : (∑ n ∈ Finset.range (wickJointCoreCutoff u v),∑ k : Fin 4,
      wickChannelKernelL1Seminorm a n k (wickCoreChannelStateKernel n u v k))≤
        (∑ k : Fin 4,wickLeftChannelCoreSeminorm a k u)*wickOriginalRightCoreSeminorm a v := by
    rw [Finset.sum_comm,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k hk
    apply (wick_actual_channel_finite_sum_bound a k u v _).trans
    apply mul_le_mul_of_nonneg_left _ (apply_nonneg _ _)
    change _≤(∑ l : Fin 4,wickRightChannelCoreSeminorm a l) v
    rw [wick_seminorm_sum_apply]
    exact Finset.single_le_sum (fun l _ => apply_nonneg (wickRightChannelCoreSeminorm a l) v) hk
  apply (mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans_eq
  simp only [wickOriginalLeftCoreSeminorm,Seminorm.smul_apply,wick_seminorm_sum_apply,NNReal.smul_def,smul_eq_mul,wickAmplitudeNormSquared,NNReal.coe_mk]
  ring

end AASCKleinGordon
