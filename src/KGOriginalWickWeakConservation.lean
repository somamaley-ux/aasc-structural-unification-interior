import KGWickLocalIntegrationByParts

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory
open scoped SchwartzMap BigOperators
namespace AASCKleinGordon

theorem original_wick_stress_derivative_test_integrable (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (i j : Fin 4) (d : Spacetime) (h : 𝓢(Spacetime,ℂ)) :
    Integrable (fun x => h x*fderiv ℝ
      (fun y => originalWickScalarStressRaisedMatrix a s u v i j y) x d) := by
  let S := (Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4))
  have hi : ∀ k∈S,Integrable (fun x => wickCoreChannelCoefficient k.1 k.2*
      (h x*fderiv ℝ (wickCoreRaisedStressMatrix a k.1 u v k.2 i j) x d)) := by
    intro k hk
    exact (wick_core_stress_directional_test_integrable a k.1 u v k.2 i j d h).const_mul _
  have hh := (integrable_finset_sum S hi).const_mul ((s : ℂ)^2)
  convert hh using 1
  funext x
  rw [original_wick_raised_stress_derivative_channel_expansion]
  change h x*((s : ℂ)^2*∑ k∈S,wickCoreChannelCoefficient k.1 k.2*
      fderiv ℝ (wickCoreRaisedStressMatrix a k.1 u v k.2 i j) x d)=_
  calc
    _ = (s : ℂ)^2*(h x*∑ k∈S,wickCoreChannelCoefficient k.1 k.2*
      fderiv ℝ (wickCoreRaisedStressMatrix a k.1 u v k.2 i j) x d) := by ring
    _ = _ := by
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      ring

theorem original_wick_stress_directional_test_pairing (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (i j : Fin 4) (d : Spacetime) (h : 𝓢(Spacetime,ℂ)) :
    (∫ x,h x*fderiv ℝ (fun y => originalWickScalarStressRaisedMatrix a s u v i j y) x d)=
      -(∫ x,wickDirectionalTestCLM d h x*originalWickScalarStressRaisedMatrix a s u v i j x) := by
  let S := (Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4))
  have hp (x : Spacetime) : h x*fderiv ℝ
      (fun y => originalWickScalarStressRaisedMatrix a s u v i j y) x d=
      (s : ℂ)^2*(h x*∑ k∈S,wickCoreChannelCoefficient k.1 k.2*
        fderiv ℝ (wickCoreRaisedStressMatrix a k.1 u v k.2 i j) x d) := by
    rw [original_wick_raised_stress_derivative_channel_expansion]
    ring
  have hq (x : Spacetime) : wickDirectionalTestCLM d h x*originalWickScalarStressRaisedMatrix a s u v i j x=
      (s : ℂ)^2*(wickDirectionalTestCLM d h x*∑ k∈S,wickCoreChannelCoefficient k.1 k.2*
        wickCoreRaisedStressMatrix a k.1 u v k.2 i j x) := by
    rw [original_wick_raised_stress_channel_expansion]
    ring
  simp_rw [hp,hq,integral_const_mul]
  rw [wick_finite_local_test_sum S (fun k => wickCoreChannelCoefficient k.1 k.2)
      (fun k x => fderiv ℝ (wickCoreRaisedStressMatrix a k.1 u v k.2 i j) x d) h
        (fun k hk => wick_core_stress_directional_test_integrable a k.1 u v k.2 i j d h),
    wick_finite_local_test_sum S (fun k => wickCoreChannelCoefficient k.1 k.2)
      (fun k => wickCoreRaisedStressMatrix a k.1 u v k.2 i j) (wickDirectionalTestCLM d h)
        (fun k hk => wick_core_stress_test_integrable a k.1 u v k.2 i j (wickDirectionalTestCLM d h))]
  simp_rw [wick_core_stress_directional_test_pairing,mul_neg]
  rw [Finset.sum_neg_distrib]
  ring

theorem original_wick_stress_distribution_conserved (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (j : Fin 4) (h : 𝓢(Spacetime,ℂ)) :
    (∑ i,originalWickRaisedStressDistribution a s u v i j
      (wickDirectionalTestCLM (spacetimeCoordinateVector i) h))=0 := by
  have heq (i : Fin 4) : originalWickRaisedStressDistribution a s u v i j
      (wickDirectionalTestCLM (spacetimeCoordinateVector i) h)=
      -(∫ x,h x*fderiv ℝ (fun y => originalWickScalarStressRaisedMatrix a s u v i j y)
        x (spacetimeCoordinateVector i)) := by
    rw [original_wick_raised_stress_distribution_pairing]
    exact (neg_eq_iff_eq_neg).mp
      (original_wick_stress_directional_test_pairing a s u v i j (spacetimeCoordinateVector i) h).symm
  simp_rw [heq]
  rw [Finset.sum_neg_distrib]
  have hi : ∀ i∈(Finset.univ : Finset (Fin 4)),Integrable (fun x => h x*fderiv ℝ
      (fun y => originalWickScalarStressRaisedMatrix a s u v i j y) x (spacetimeCoordinateVector i)) :=
    fun i _ => original_wick_stress_derivative_test_integrable a s u v i j (spacetimeCoordinateVector i) h
  rw [← integral_finset_sum _ hi]
  simp_rw [← Finset.mul_sum,original_wick_scalar_stress_conserved]
  simp

end AASCKleinGordon
