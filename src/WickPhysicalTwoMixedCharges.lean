import WickPhysicalMixedChargeDiagonal
import WickPhysicalMarginalIntegrability

noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

theorem wick_original_two_mixed_spectator_coefficient (a : Parameters) (s : ℝ) (n : ℕ)
    (u v : FiniteParticleCore) (j : Fin 4) (p : Momentum) :
    (s : ℂ)^2*(a.speed : ℂ)⁻¹*(wickSpatialFourierJacobian a : ℂ)*(wignerWeight a p : ℂ)^2*
      (wickCoreChannelCoefficient n 1 *
        ∫ r,wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n 1)
          (wickCoreChannelFrequency1 a n 1) (wickCoreChannelStateKernel n u v 1) 0 j
          (Fin.cons p (Fin.cons p r)) ∂particleMeasure a n +
       wickCoreChannelCoefficient n 2 *
        ∫ r,wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n 2)
          (wickCoreChannelFrequency1 a n 2) (wickCoreChannelStateKernel n u v 2) 0 j
          (Fin.cons p (Fin.cons p r)) ∂particleMeasure a n)=
      wickSameTensorChargeCoefficient a s*((n+1 : ℝ) : ℂ)*
        ∫ r,(wignerWeight a p : ℂ)*(massShell a p j : ℂ)*
          wickCoreChannelStateKernel n u v 1 (Fin.cons p (Fin.cons p r)) ∂particleMeasure a n := by
  let K₁ := wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n 1)
    (wickCoreChannelFrequency1 a n 1) (wickCoreChannelStateKernel n u v 1) 0 j
  let K₂ := wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n 2)
    (wickCoreChannelFrequency1 a n 2) (wickCoreChannelStateKernel n u v 2) 0 j
  have i₁ := wick_physical_pair_spectator_integrable a n K₁ p p
  have i₂ := wick_physical_pair_spectator_integrable a n K₂ p p
  calc
    _ = ∫ r,(s : ℂ)^2*(a.speed : ℂ)⁻¹*(wickSpatialFourierJacobian a : ℂ)*(wignerWeight a p : ℂ)^2*
        (wickCoreChannelCoefficient n 1*K₁ (Fin.cons p (Fin.cons p r))+
          wickCoreChannelCoefficient n 2*K₂ (Fin.cons p (Fin.cons p r))) ∂particleMeasure a n := by
      rw [integral_const_mul,integral_add (i₁.const_mul _) (i₂.const_mul _),
        integral_const_mul,integral_const_mul]
    _ = ∫ r,(wickSameTensorChargeCoefficient a s*((n+1 : ℝ) : ℂ))*
        ((wignerWeight a p : ℂ)*(massShell a p j : ℂ)*
          wickCoreChannelStateKernel n u v 1 (Fin.cons p (Fin.cons p r))) ∂particleMeasure a n := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun r => by
        simpa only [K₁,K₂,mul_assoc] using wick_same_tensor_both_CA_charge_coefficients a s n
          (wickCoreChannelStateKernel n u v 1) (Fin.cons p (Fin.cons p r)) rfl j)
    _ = _ := integral_const_mul _ _

theorem wick_original_two_mixed_hypersurface_charges (a : Parameters) (s : ℝ) (n : ℕ)
    (u v : FiniteParticleCore) (j : Fin 4) (τ : ℝ) :
    (s : ℂ)^2*(a.speed : ℂ)⁻¹*
      (wickCoreChannelCoefficient n 1 *
        (∫ x : WickSpaceSlice,wickCoreRaisedStressMatrix a n u v 1 0 j (spacetimeSpatialJoin (τ,x)))+
       wickCoreChannelCoefficient n 2 *
        (∫ x : WickSpaceSlice,wickCoreRaisedStressMatrix a n u v 2 0 j (spacetimeSpatialJoin (τ,x))))=
      wickSameTensorChargeCoefficient a s*((n+1 : ℝ) : ℂ)*
        ∫ p : Momentum,∫ r,(wignerWeight a p : ℂ)*(massShell a p j : ℂ)*
          wickCoreChannelStateKernel n u v 1 (Fin.cons p (Fin.cons p r)) ∂particleMeasure a n := by
  let K₁ := wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n 1)
    (wickCoreChannelFrequency1 a n 1) (wickCoreChannelStateKernel n u v 1) 0 j
  let K₂ := wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n 2)
    (wickCoreChannelFrequency1 a n 2) (wickCoreChannelStateKernel n u v 2) 0 j
  let f₁ := fun p : Momentum => (wignerWeight a p : ℂ)^2*
    ∫ r,K₁ (Fin.cons p (Fin.cons p r)) ∂particleMeasure a n
  let f₂ := fun p : Momentum => (wignerWeight a p : ℂ)^2*
    ∫ r,K₂ (Fin.cons p (Fin.cons p r)) ∂particleMeasure a n
  have i₁ : Integrable f₁ := wick_original_mixed_diagonal_momentum_integrable a n u v 1 j
  have i₂ : Integrable f₂ := wick_original_mixed_diagonal_momentum_integrable a n u v 2 j
  rw [wick_original_mixed_hypersurface_integral a n u v 1 j (Or.inl rfl) τ,
    wick_original_mixed_hypersurface_integral a n u v 2 j (Or.inr rfl) τ]
  change (s : ℂ)^2*(a.speed : ℂ)⁻¹*
    (wickCoreChannelCoefficient n 1*((wickSpatialFourierJacobian a : ℂ)*∫ p,f₁ p)+
      wickCoreChannelCoefficient n 2*((wickSpatialFourierJacobian a : ℂ)*∫ p,f₂ p))=_
  calc
    _ = ∫ p : Momentum,((s : ℂ)^2*(a.speed : ℂ)⁻¹*(wickSpatialFourierJacobian a : ℂ))*
        (wickCoreChannelCoefficient n 1*f₁ p+wickCoreChannelCoefficient n 2*f₂ p) := by
      rw [integral_const_mul,integral_add (i₁.const_mul _) (i₂.const_mul _),
        integral_const_mul,integral_const_mul]
      ring
    _ = ∫ p : Momentum,(wickSameTensorChargeCoefficient a s*((n+1 : ℝ) : ℂ))*
        ∫ r,(wignerWeight a p : ℂ)*(massShell a p j : ℂ)*
          wickCoreChannelStateKernel n u v 1 (Fin.cons p (Fin.cons p r)) ∂particleMeasure a n := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => by
        have same := wick_original_two_mixed_spectator_coefficient a s n u v j p
        dsimp only [f₁,f₂,K₁,K₂]
        convert same using 1 <;> ring)
    _ = _ := integral_const_mul _ _

end AASCKleinGordon
