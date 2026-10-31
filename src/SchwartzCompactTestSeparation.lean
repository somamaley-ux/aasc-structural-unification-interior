import SchwartzCutoffConvergence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Filter Topology
open scoped SchwartzMap
namespace AASCKleinGordon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem wick_compact_schwartz_dense :
    Dense {f : 𝓢(E,ℂ) | HasCompactSupport f} := by
  intro f
  apply isClosed_closure.mem_of_tendsto (wick_schwartz_cutoff_sequence_tendsto f)
  exact Eventually.of_forall fun N => subset_closure (wick_schwartz_cutoff_sequence_compact f N)

/-- Arbitrary continuous Schwartz distributions are separated by compact
Schwartz tests. Pure-pair separation needs a further tensor approximation. -/
theorem wick_compact_schwartz_distribution_ext
    (A B : 𝓢(E,ℂ) →L[ℂ] ℂ)
    (h : ∀ f : 𝓢(E,ℂ),HasCompactSupport f → A f=B f) : A=B := by
  apply ContinuousLinearMap.ext
  intro f
  have hA := (A.continuous.tendsto f).comp (wick_schwartz_cutoff_sequence_tendsto f)
  have hB := (B.continuous.tendsto f).comp (wick_schwartz_cutoff_sequence_tendsto f)
  have hBA : Tendsto (fun N => A (wickSchwartzCutoffSequence f N)) atTop (𝓝 (B f)) :=
    hB.congr' (Eventually.of_forall fun N =>
      (h _ (wick_schwartz_cutoff_sequence_compact f N)).symm)
  exact tendsto_nhds_unique hA hBA

theorem wick_compact_schwartz_distribution_zero
    (A : 𝓢(E,ℂ) →L[ℂ] ℂ)
    (h : ∀ f : 𝓢(E,ℂ),HasCompactSupport f → A f=0) : A=0 := by
  apply wick_compact_schwartz_distribution_ext A 0
  intro f hf
  exact h f hf

theorem wick_covariant_kernel_cutoff_pairing_tendsto (a : Parameters) (s : ℝ)
    (i j : Fin 4) (h : 𝓢(Spacetime,ℂ)) (G : 𝓢(ParticleConfiguration 2,ℂ)) :
    Tendsto (fun N => wickCovariantKernelMomentumCLM a s i j h (wickSchwartzCutoffSequence G N))
      atTop (𝓝 (wickCovariantKernelMomentumCLM a s i j h G)) :=
  ((wickCovariantKernelMomentumCLM a s i j h).continuous.tendsto G).comp
    (wick_schwartz_cutoff_sequence_tendsto G)

/-- A bounded native continuation uniqueness result with its exact datum:
agreement on ALL compact two-momentum Schwartz tests. Agreement only on
pure wavepacket pairs is not substituted for this premise. -/
theorem wick_covariant_kernel_compact_continuation_unique (a : Parameters) (s : ℝ)
    (i j : Fin 4) (h : 𝓢(Spacetime,ℂ))
    (B : 𝓢(ParticleConfiguration 2,ℂ) →L[ℂ] ℂ)
    (hB : ∀ G : 𝓢(ParticleConfiguration 2,ℂ),HasCompactSupport G →
      B G=wickCovariantKernelMomentumCLM a s i j h G) :
    B=wickCovariantKernelMomentumCLM a s i j h :=
  wick_compact_schwartz_distribution_ext B _ hB

end AASCKleinGordon
