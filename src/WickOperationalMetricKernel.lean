import WickCovariantUnitNormalization
import WickKGOriginalActionReality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open TopologicalSpace
open AASCSemanticExhaustion
open scoped SchwartzMap BigOperators
namespace AASCKleinGordon
attribute [local irreducible] originalWickRaisedStressDistribution wickCovariantOriginalCore

theorem wick_operational_original_stress_components (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (k : WickSchwartzMetricTest) :
    originalWickStressMetricDistribution a s u v k =
      ∑ i : Fin 4, ∑ j : Fin 4, originalWickRaisedStressDistribution a s u v i j (k i j) := by
  simp only [originalWickStressMetricDistribution, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

theorem wick_operational_original_diagonal_real_part (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) :
    (originalWickNativeMetricResponse a s u u Ω H).re =
      originalWickNativeRealMetricResponse a s u Ω H := rfl

/-- The original action response is HALF the full stress pairing, retaining
all sixteen original compact-real-metric-test components. -/
def wickOperationalMetricKernel (a : Parameters) (s : ℝ)
    {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) :
    𝓢(ParticleConfiguration 2,ℂ) →L[ℂ] ℂ :=
  (1/2 : ℂ) • ∑ i : Fin 4, ∑ j : Fin 4,
    wickCovariantKernelMomentumCLM a s i j (nativeToWickMetricTest Ω H i j)

theorem wick_operational_metric_kernel_pair (a : Parameters) (s : ℝ)
    {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) (f g : 𝓢(Momentum,ℂ)) :
    wickOperationalMetricKernel a s H (wickCovariantPairTest f g) =
      originalWickNativeMetricResponse a s (wickCovariantOriginalCore a f)
        (wickCovariantOriginalCore a g) Ω H := by
  rw [wickOperationalMetricKernel, ContinuousLinearMap.smul_apply, smul_eq_mul,
    original_wick_native_metric_response_half_pairing,
    wick_operational_original_stress_components]
  simp only [ContinuousLinearMap.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact (wick_covariant_strong_kernel_square a s i j f g _).trans
    (wick_covariant_strong_source_same_tensor a s i j f g _)

theorem wick_original_native_response_diagonal_real (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) :
    (originalWickNativeMetricResponse a s u u Ω H).im = 0 := by
  have hd : HasDerivAt (fun t : ℝ => wickOriginalFiniteAction a s u u (t • H))
      (originalWickNativeMetricResponse a s u u Ω H) 0 := by
    exact wick_original_finite_action_gateaux_derivative a s u u Ω H
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hd
  have hz : (fun t : ℝ => (wickOriginalFiniteAction a s u u (t • H)).im) =
      fun _ => (0 : ℝ) := funext (fun t => wick_original_finite_action_diagonal_real a s u (t • H))
  change HasDerivAt (fun t : ℝ => (wickOriginalFiniteAction a s u u (t • H)).im)
    (originalWickNativeMetricResponse a s u u Ω H).im 0 at hi
  rw [hz] at hi
  exact hi.unique (hasDerivAt_const 0 (0 : ℝ))

theorem wick_operational_metric_kernel_diagonal_real (a : Parameters) (s : ℝ)
    {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) (f : 𝓢(Momentum,ℂ)) :
    (wickOperationalMetricKernel a s H (wickCovariantPairTest f f)).im = 0 := by
  rw [wick_operational_metric_kernel_pair]
  exact wick_original_native_response_diagonal_real a s _ H

theorem wick_operational_metric_kernel_first_readout (a : Parameters) (s : ℝ)
    {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) (f : 𝓢(Momentum,ℂ)) :
    (wickOperationalMetricKernel a s H (wickCovariantPairTest f f)).re =
      wickKGFirstOutput a s (wickCovariantOriginalCore a f) (wickKGIdentityAct H) := by
  rw [wick_operational_metric_kernel_pair, wick_KG_original_first_output_computed,
    wick_KG_identity_tangent]
  rfl

theorem wick_operational_metric_kernel_complex_diagonal (a : Parameters) (s : ℝ)
    {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) (f : 𝓢(Momentum,ℂ)) :
    wickOperationalMetricKernel a s H (wickCovariantPairTest f f) =
      (wickKGFirstOutput a s (wickCovariantOriginalCore a f) (wickKGIdentityAct H) : ℂ) := by
  apply Complex.ext
  · exact wick_operational_metric_kernel_first_readout a s H f
  · simpa only [Complex.ofReal_im] using wick_operational_metric_kernel_diagonal_real a s H f

theorem wick_operational_metric_kernel_normalized_ray_readout (a : Parameters) (s : ℝ)
    {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω)
    (f : 𝓢(Momentum,ℂ)) (hf : f ≠ 0) :
    (wickOperationalMetricKernel a s H
      (wickCovariantPairTest (wickCovariantUnitTest a f) (wickCovariantUnitTest a f))).re =
      originalWickRayMetricResponse a s Ω
        (Quotient.mk wickCoreRaySetoid
          ⟨wickCovariantOriginalCore a f, wick_covariant_original_core_nonzero a f hf⟩) H := by
  rw [wick_operational_metric_kernel_pair, wick_operational_original_diagonal_real_part]
  have st := congrArg (fun u : FiniteParticleCore => originalWickNativeRealMetricResponse a s u Ω)
    (wick_covariant_unit_test_original_square a f)
  have ray := original_wick_ray_source_is_actual_unit_response a s Ω
    ⟨wickCovariantOriginalCore a f, wick_covariant_original_core_nonzero a f hf⟩
  exact DFunLike.congr_fun (st.trans ray.symm) H

theorem wick_operational_metric_kernel_full_stress (a : Parameters) (s : ℝ)
    {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) (f g : 𝓢(Momentum,ℂ)) :
    (2 : ℂ) * wickOperationalMetricKernel a s H (wickCovariantPairTest f g) =
      originalWickStressMetricDistribution a s (wickCovariantOriginalCore a f)
        (wickCovariantOriginalCore a g) (nativeToWickMetricTest Ω H) := by
  rw [wick_operational_metric_kernel_pair, original_wick_native_metric_response_half_pairing]
  ring

end AASCKleinGordon
