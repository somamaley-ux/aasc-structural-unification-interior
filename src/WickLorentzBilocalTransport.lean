import WickPoincarePairTransport

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

theorem wick_core_lorentz_component (a : Parameters) (L : ProperLorentzTransform)
    (u : FiniteParticleCore) (n : ℕ) (z : ParticleConfiguration n) :
    ((coreLorentz a L u) n).val z = (u n).val (particleLorentzMap a n L⁻¹ z) := rfl

theorem wick_lorentz_map_tail (a : Parameters) (L : ProperLorentzTransform)
    (n : ℕ) (z : ParticleConfiguration (n+1)) :
    particleLorentzMap a n L (Fin.tail z)=Fin.tail (particleLorentzMap a (n+1) L z) := rfl

theorem wick_lorentz_map_cons (a : Parameters) (L : ProperLorentzTransform)
    (n : ℕ) (p : Momentum) (z : ParticleConfiguration n) :
    particleLorentzMap a (n+1) L (Fin.cons p z)=
      Fin.cons (lorentzShellMap a L p) (particleLorentzMap a n L z) := by
  ext i
  cases i using Fin.cases <;> rfl

theorem wick_lorentz_map_apply (a : Parameters) (L : ProperLorentzTransform)
    (n : ℕ) (z : ParticleConfiguration n) (i : Fin n) :
    particleLorentzMap a n L z i=lorentzShellMap a L (z i) := rfl

theorem wick_lorentz_channel_kernel (a : Parameters) (L : ProperLorentzTransform)
    (n : ℕ) (u v : FiniteParticleCore) (i : Fin 4) (z : ParticleConfiguration (n+2)) :
    wickCoreChannelStateKernel n (coreLorentz a L u) (coreLorentz a L v) i z =
      wickCoreChannelStateKernel n u v i (particleLorentzMap a (n+2) L⁻¹ z) := by
  fin_cases i <;> simp [wickCoreChannelStateKernel,
    wickAAStateKernel_apply, wickMixedStateKernel_apply, SchwartzOperations.conjugateSchwartzCLM_apply,
    wick_core_lorentz_component, wick_lorentz_map_cons, wick_lorentz_map_tail,
    wick_lorentz_map_apply]

theorem wick_lorentz_tail_bound (a : Parameters) (L : ProperLorentzTransform)
    (u : FiniteParticleCore) (N : ℕ) (bound : WickCoreTailBound u N) :
    WickCoreTailBound (coreLorentz a L u) N := by
  intro n hn
  change bosonicLorentzSchwartzCLM a n L (u n)=0
  rw [bound n hn, map_zero]

theorem wick_lorentz_frequency0_pairing (a : Parameters) (L : ProperLorentzTransform)
    (n : ℕ) (i : Fin 4) (x : Spacetime) (z : ParticleConfiguration (n+2)) :
    inner ℝ (spacetimeLorentzCLE L x) (wickCoreChannelFrequency0 a n i z) =
      inner ℝ x (wickCoreChannelFrequency0 a n i (particleLorentzMap a (n+2) L⁻¹ z)) := by
  fin_cases i <;> simp [wickCoreChannelFrequency0, Fin.cons_zero, Fin.cons_succ,
    Pi.neg_apply, inner_neg_right, wickShellFrequencyAt, shellFrequency, inner_smul_right,
    spacetimeLorentz_inner_shellCovector, particleLorentzMap]

theorem wick_lorentz_frequency1_pairing (a : Parameters) (L : ProperLorentzTransform)
    (n : ℕ) (i : Fin 4) (x : Spacetime) (z : ParticleConfiguration (n+2)) :
    inner ℝ (spacetimeLorentzCLE L x) (wickCoreChannelFrequency1 a n i z) =
      inner ℝ x (wickCoreChannelFrequency1 a n i (particleLorentzMap a (n+2) L⁻¹ z)) := by
  fin_cases i <;> simp [wickCoreChannelFrequency1, Fin.cons_zero, Fin.cons_succ,
    Pi.neg_apply, inner_neg_right, wickShellFrequencyAt, shellFrequency, inner_smul_right,
    spacetimeLorentz_inner_shellCovector, particleLorentzMap]

theorem wick_original_channel_matrix_lorentz (a : Parameters) (L : ProperLorentzTransform)
    (n : ℕ) (u v : FiniteParticleCore) (i : Fin 4) (x y : Spacetime) :
    wickCoreChannelMatrix a n (coreLorentz a L u) (coreLorentz a L v) i
      (spacetimeLorentzCLE L x) (spacetimeLorentzCLE L y) =
      wickCoreChannelMatrix a n u v i x y := by
  unfold wickCoreChannelMatrix
  rw [wickBilocalMatrix_formula a (n+2) _ _ (wickCoreChannelFrequency1_temperate a n i),
    wickBilocalMatrix_formula a (n+2) _ _ (wickCoreChannelFrequency1_temperate a n i)]
  simp_rw [wick_lorentz_channel_kernel, wick_lorentz_frequency0_pairing,
    wick_lorentz_frequency1_pairing]
  have integral := (particleLorentz_preserves_measure a (n+2) L⁻¹).integral_comp
    (particleLorentzME a (n+2) L⁻¹).measurableEmbedding
    (fun z : ParticleConfiguration (n+2) =>
      Real.fourierChar (-inner ℝ x (wickCoreChannelFrequency0 a n i z)) •
        (Real.fourierChar (-inner ℝ y (wickCoreChannelFrequency1 a n i z)) •
          (wickCoreChannelStateKernel n u v i z : ℂ)))
  exact integral

theorem wick_original_bilocal_lorentz (a : Parameters) (L : ProperLorentzTransform)
    (s : ℝ) (u v : FiniteParticleCore) (x y : Spacetime) :
    originalWickBilocalCore a s (coreLorentz a L u) (coreLorentz a L v)
      (spacetimeLorentzCLE L x) (spacetimeLorentzCLE L y) =
      originalWickBilocalCore a s u v x y := by
  let N := wickJointCoreCutoff u v
  have hu : WickCoreTailBound u N :=
    (wickCoreTailBound_cutoff u).mono (le_max_left _ _)
  have hv : WickCoreTailBound v N :=
    (wickCoreTailBound_cutoff v).mono (le_max_right _ _)
  rw [originalWickBilocalCore_eq_any_cutoff a s _ _ N
    (wick_lorentz_tail_bound a L u N hu) (wick_lorentz_tail_bound a L v N hv),
    originalWickBilocalCore_eq_any_cutoff a s u v N hu hv]
  unfold originalWickBilocalCoreAt
  simp_rw [wick_original_channel_matrix_lorentz]

theorem wick_original_square_lorentz (a : Parameters) (L : ProperLorentzTransform)
    (s : ℝ) (u v : FiniteParticleCore) (x : Spacetime) :
    originalWickSquareMatrix a s (coreLorentz a L u) (coreLorentz a L v)
      (spacetimeLorentzCLE L x) = originalWickSquareMatrix a s u v x :=
  wick_original_bilocal_lorentz a L s u v x x

end AASCKleinGordon
