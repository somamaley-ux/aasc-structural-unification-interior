import WickOperationalMetricKernel
import SchwartzPurePairSeparation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
open TopologicalSpace
open AASCSemanticExhaustion
open scoped SchwartzMap
namespace AASCKleinGordon

theorem wick_covariant_pair_zero :
    wickCovariantPairTest (0 : 𝓢(Momentum,ℂ)) 0 = 0 := by
  ext z
  simp only [wick_covariant_pair_test_apply, SchwartzMap.zero_apply, star_zero, zero_mul]

theorem wick_covariant_pair_diagonal_smul (c : ℂ) (f : 𝓢(Momentum,ℂ)) :
    wickCovariantPairTest (c • f) (c • f) =
      (star c * c) • wickCovariantPairTest f f := by
  ext z
  simp only [wick_covariant_pair_test_apply, SchwartzMap.smul_apply, smul_eq_mul, star_mul]
  ring

/-- Polarization in the ACTUAL two-momentum Schwartz test space; the first
state slot is conjugate linear. No off-diagonal bridge is assumed. -/
theorem wick_covariant_pair_polarization (f g : 𝓢(Momentum,ℂ)) :
    wickCovariantPairTest f g = (1/4 : ℂ) •
      (wickCovariantPairTest (f+g) (f+g) - wickCovariantPairTest (f-g) (f-g) -
        Complex.I • wickCovariantPairTest (f+Complex.I • g) (f+Complex.I • g) +
        Complex.I • wickCovariantPairTest (f-Complex.I • g) (f-Complex.I • g)) := by
  ext z
  simp only [wick_covariant_pair_test_apply, SchwartzMap.smul_apply,
    SchwartzMap.add_apply, SchwartzMap.sub_apply, smul_eq_mul,
    star_add, star_sub, star_mul, Complex.star_def, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Physical normalization uses the existing covariant Hilbert embedding;
it does not impose a norm on Schwartz space. -/
theorem wick_unit_diagonal_distribution_ext (a : Parameters)
    (A B : 𝓢(ParticleConfiguration 2,ℂ) →L[ℂ] ℂ)
    (hunit : ∀ f : 𝓢(Momentum,ℂ), ‖wickCovariantNaturalTest a f‖ = 1 →
      A (wickCovariantPairTest f f) = B (wickCovariantPairTest f f)) : A = B := by
  have hdiag (f : 𝓢(Momentum,ℂ)) :
      A (wickCovariantPairTest f f) = B (wickCovariantPairTest f f) := by
    by_cases hf : f = 0
    · subst f
      rw [wick_covariant_pair_zero, map_zero, map_zero]
    · have h := hunit (wickCovariantUnitTest a f) (wick_covariant_unit_test_norm a f hf)
      let c : ℂ := ((‖wickCovariantNaturalTest a f‖⁻¹ : ℝ) : ℂ)
      have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr
        (inv_ne_zero (wick_covariant_natural_norm_positive a f hf).ne')
      have hcc : star c * c ≠ 0 := mul_ne_zero (star_ne_zero.mpr hc) hc
      change A (wickCovariantPairTest (c • f) (c • f)) =
        B (wickCovariantPairTest (c • f) (c • f)) at h
      rw [wick_covariant_pair_diagonal_smul, map_smul, map_smul] at h
      exact mul_left_cancel₀ hcc h
  apply wick_pure_pair_distribution_ext
  intro f g
  conv_lhs => rw [wick_covariant_pair_polarization f g]
  conv_rhs => rw [wick_covariant_pair_polarization f g]
  simp only [map_smul, map_add, map_sub]
  rw [hdiag (f+g), hdiag (f-g), hdiag (f+Complex.I • g), hdiag (f-Complex.I • g)]

def WickUnitDiagonalReality (a : Parameters)
    (B : 𝓢(ParticleConfiguration 2,ℂ) →L[ℂ] ℂ) : Prop :=
  ∀ f : 𝓢(Momentum,ℂ), ‖wickCovariantNaturalTest a f‖ = 1 →
    (B (wickCovariantPairTest f f)).im = 0

def WickUnitFirstReadoutAgreement (a : Parameters) (s : ℝ)
    {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω)
    (B : 𝓢(ParticleConfiguration 2,ℂ) →L[ℂ] ℂ) : Prop :=
  ∀ f : 𝓢(Momentum,ℂ), ‖wickCovariantNaturalTest a f‖ = 1 →
    (B (wickCovariantPairTest f f)).re =
      wickKGFirstOutput a s (wickCovariantOriginalCore a f) (wickKGIdentityAct H)

theorem wick_operational_kernel_unique_from_unit_first_readouts (a : Parameters) (s : ℝ)
    {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω)
    (B : 𝓢(ParticleConfiguration 2,ℂ) →L[ℂ] ℂ)
    (reality : WickUnitDiagonalReality a B)
    (readouts : WickUnitFirstReadoutAgreement a s H B) :
    B = wickOperationalMetricKernel a s H := by
  apply wick_unit_diagonal_distribution_ext a
  intro f hf
  apply Complex.ext
  · exact (readouts f hf).trans (wick_operational_metric_kernel_first_readout a s H f).symm
  · exact (reality f hf).trans (wick_operational_metric_kernel_diagonal_real a s H f).symm

/-- The original real first-action readouts, with separately stated diagonal
reality, determine exactly one continuous complex kernel. Existence is the
constructed half-contracted native kernel, not an assumed source bridge. -/
theorem wick_operational_kernel_exists_unique_from_unit_first_readouts
    (a : Parameters) (s : ℝ) {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) :
    ∃! B : 𝓢(ParticleConfiguration 2,ℂ) →L[ℂ] ℂ,
      WickUnitDiagonalReality a B ∧ WickUnitFirstReadoutAgreement a s H B := by
  refine ⟨wickOperationalMetricKernel a s H, ⟨?_, ?_⟩, ?_⟩
  · exact fun f _ => wick_operational_metric_kernel_diagonal_real a s H f
  · exact fun f _ => wick_operational_metric_kernel_first_readout a s H f
  · exact fun B hB => wick_operational_kernel_unique_from_unit_first_readouts a s H B hB.1 hB.2

end AASCKleinGordon
