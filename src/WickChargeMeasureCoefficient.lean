import WickOriginalChargeKernels

noncomputable section
set_option maxHeartbeats 1500000
open scoped SchwartzMap
namespace AASCKleinGordon

def wickSpatialFourierJacobian (a : Parameters) : ℝ := (fourierWaveScale a)⁻¹^3

def wickSameTensorChargeCoefficient (a : Parameters) (s : ℝ) : ℂ :=
  2*(s : ℂ)^2*(wickSpatialFourierJacobian a : ℂ)*(a.mass : ℂ)/(a.hbar : ℂ)^2

theorem wick_spatial_fourier_jacobian_value (a : Parameters) :
    wickSpatialFourierJacobian a=(2*Real.pi*a.hbar)^3 := by
  simp only [wickSpatialFourierJacobian, fourierWaveScale, inv_inv]

theorem wick_wigner_charge_density_coefficient (a : Parameters) (p : Momentum) (j : Fin 4) :
    (a.speed : ℂ)⁻¹*(wickSpatialFourierJacobian a : ℂ)*(wignerWeight a p : ℂ)^2*
      ((massShell a p 0 : ℂ)*(massShell a p j : ℂ)/(a.hbar : ℂ)^2) =
      ((wickSpatialFourierJacobian a : ℂ)*(a.mass : ℂ)/(a.hbar : ℂ)^2)*
        (wignerWeight a p : ℂ)*(massShell a p j : ℂ) := by
  have energy_ne : (energy a p : ℂ)≠0 := by exact_mod_cast (energy_pos a p).ne'
  have speed_ne : (a.speed : ℂ)≠0 := by exact_mod_cast a.speed_pos.ne'
  have hbar_ne : (a.hbar : ℂ)≠0 := by exact_mod_cast a.hbar_pos.ne'
  have time : massShell a p 0=energy a p/a.speed := rfl
  rw [time]
  unfold wignerWeight
  push_cast
  field_simp
  <;> ring

theorem wick_same_tensor_both_CA_charge_coefficients (a : Parameters) (s : ℝ) (n : ℕ)
    (G : 𝓢(ParticleConfiguration (n+2),ℂ)) (z : ParticleConfiguration (n+2))
    (diagonal : z 1=z 0) (j : Fin 4) :
    (s : ℂ)^2*(a.speed : ℂ)⁻¹*(wickSpatialFourierJacobian a : ℂ)*
      (wignerWeight a (z 0) : ℂ)^2 *
      (wickCoreChannelCoefficient n 1 *
        wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n 1)
          (wickCoreChannelFrequency1 a n 1) G 0 j z +
       wickCoreChannelCoefficient n 2 *
        wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n 2)
          (wickCoreChannelFrequency1 a n 2) G 0 j z) =
      wickSameTensorChargeCoefficient a s * ((n+1 : ℝ) : ℂ) *
        (wignerWeight a (z 0) : ℂ)*(massShell a (z 0) j : ℂ)*G z := by
  rw [wick_original_CA_kernel_momentum_diagonal a n G z diagonal,
    wick_original_reversed_CA_kernel_momentum_diagonal a n G z diagonal]
  have coefficient := wick_wigner_charge_density_coefficient a (z 0) j
  have first : wickCoreChannelCoefficient n 1=((n+1 : ℝ) : ℂ) := rfl
  have second : wickCoreChannelCoefficient n 2=((n+1 : ℝ) : ℂ) := rfl
  rw [first,second]
  unfold wickSameTensorChargeCoefficient
  linear_combination (2*(s : ℂ)^2*((n+1 : ℝ) : ℂ)*G z)*coefficient

theorem wick_same_tensor_charge_coefficient_zero_amplitude (a : Parameters) :
    wickSameTensorChargeCoefficient a 0=0 := by
  simp [wickSameTensorChargeCoefficient]

end AASCKleinGordon
