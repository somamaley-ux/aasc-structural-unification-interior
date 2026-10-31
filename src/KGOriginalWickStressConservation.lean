import KGOriginalWickStressChannels

/-! Divergence of the SAME action-identified quantum tensor on every original
finite-core state pair. Actual finite-sum differentiation is proved. -/
noncomputable section
set_option maxHeartbeats 8000000
open scoped BigOperators
namespace AASCKleinGordon

theorem original_wick_raised_stress_derivative_channel_expansion (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (i j : Fin 4) (x d : Spacetime) :
    fderiv ℝ (fun y => originalWickScalarStressRaisedMatrix a s u v i j y) x d=(s : ℂ)^2*
      ∑ k∈(Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4)),
        wickCoreChannelCoefficient k.1 k.2*fderiv ℝ (wickCoreRaisedStressMatrix a k.1 u v k.2 i j) x d := by
  simp_rw [original_wick_raised_stress_channel_expansion]
  apply wick_scaled_finite_weighted_directional_derivative
  intro k hk
  exact (wick_core_raised_stress_smooth a k.1 u v k.2 i j).differentiable (by simp) x

theorem original_wick_scalar_stress_conserved (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (j : Fin 4) (x : Spacetime) :
    (∑ i,fderiv ℝ (fun y => originalWickScalarStressRaisedMatrix a s u v i j y)
      x (spacetimeCoordinateVector i))=0 := by
  simp_rw [original_wick_raised_stress_derivative_channel_expansion]
  rw [← Finset.mul_sum,Finset.sum_comm]
  have hsum : (∑ k∈(Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4)),
      ∑ i,wickCoreChannelCoefficient k.1 k.2*
        fderiv ℝ (wickCoreRaisedStressMatrix a k.1 u v k.2 i j) x (spacetimeCoordinateVector i))=0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [← Finset.mul_sum,wick_core_raised_stress_conserved]
    simp
  rw [hsum,mul_zero]

end AASCKleinGordon
