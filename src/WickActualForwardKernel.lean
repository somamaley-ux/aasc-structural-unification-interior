import WickSourceReceiverFrontend

noncomputable section
set_option maxHeartbeats 1800000
open TopologicalSpace
open AASCSemanticExhaustion
open scoped SchwartzMap
namespace AASCKleinGordon

/-- Exact normalization between the actual original mixed stress symbol and
the displayed scalar forward tensor. This is a kernel identity, not a claim
about unconstructed generalized-state matrix elements or Breit transforms. -/
theorem wick_actual_mixed_symbol_forward_tensor (a : Parameters) (p : Momentum) (i j : Fin 4) :
    2*(a.hbar : ℂ)^2*wickRaisedStressSymbol a (shellFrequency a p) (-shellFrequency a p) i j=
      (scalarMatrixElement a (massShell a p) (massShell a p) i j : ℂ) := by
  rw [wick_original_same_stress_mixed_momentum_symbol,forward_matrix_element]
  have hh : (a.hbar : ℂ)≠0 := Complex.ofReal_ne_zero.mpr a.hbar_pos.ne'
  push_cast
  field_simp [hh] <;> ring

theorem wick_actual_CA_kernel_forward_tensor (a : Parameters) (n : ℕ)
    (G : 𝓢(ParticleConfiguration (n+2),ℂ)) (z : ParticleConfiguration (n+2))
    (diagonal : z 1=z 0) (i j : Fin 4) :
    2*(a.hbar : ℂ)^2*(wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n 1)
      (wickCoreChannelFrequency1 a n 1) G i j z)=
        (scalarMatrixElement a (massShell a (z 0)) (massShell a (z 0)) i j : ℂ)*G z := by
  rw [wick_raised_stress_kernel_apply a (n+2) _ _
    (wickCoreChannelFrequency0_temperate a n 1) (wickCoreChannelFrequency1_temperate a n 1)]
  change 2*(a.hbar : ℂ)^2*(wickRaisedStressSymbol a (shellFrequency a (z 0))
    (-shellFrequency a (z 1)) i j*G z)=_
  rw [diagonal,← mul_assoc,wick_actual_mixed_symbol_forward_tensor]

theorem wick_actual_reversed_CA_kernel_forward_tensor (a : Parameters) (n : ℕ)
    (G : 𝓢(ParticleConfiguration (n+2),ℂ)) (z : ParticleConfiguration (n+2))
    (diagonal : z 1=z 0) (i j : Fin 4) :
    2*(a.hbar : ℂ)^2*(wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n 2)
      (wickCoreChannelFrequency1 a n 2) G i j z)=
        (scalarMatrixElement a (massShell a (z 0)) (massShell a (z 0)) i j : ℂ)*G z := by
  rw [wick_raised_stress_kernel_apply a (n+2) _ _
    (wickCoreChannelFrequency0_temperate a n 2) (wickCoreChannelFrequency1_temperate a n 2)]
  change 2*(a.hbar : ℂ)^2*(wickRaisedStressSymbol a (-shellFrequency a (z 1))
    (shellFrequency a (z 0)) i j*G z)=_
  rw [diagonal,wick_same_stress_symbol_swap,← mul_assoc,wick_actual_mixed_symbol_forward_tensor]

/-- Explicit nonvacuity of the calibrated native source/inertial overlap;
the ray is supplied by the already occupied original one-particle core. -/
theorem wick_calibrated_source_role_overlap_nonempty (a : Parameters) (Ω : Opens CoordinatePoint) :
    (wickRoleQmasshat a (wickPositiveCalibratedAmplitude a) Ω).Nonempty := by
  let ray : Quotient wickCoreRaySetoid := Quotient.mk wickCoreRaySetoid
    ⟨oneParticleCore,oneParticleCore_nonzero⟩
  exact ⟨wickRolePiA a (wickPositiveCalibratedAmplitude a) Ω
    (wickRoleSx a (wickPositiveCalibratedAmplitude a) Ω ray),
      wick_role_original_source_in_mass_overlap a (wickPositiveCalibratedAmplitude a) Ω ray⟩

end AASCKleinGordon
