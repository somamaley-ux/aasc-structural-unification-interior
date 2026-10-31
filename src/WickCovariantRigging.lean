import WickCovariantUnitary
import WickWignerWeightSchwartz

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped SchwartzMap
namespace AASCKleinGordon

/-- Actual continuous momentum evaluation on the Schwartz rigging. -/
def wickMomentumEvaluation (p : Momentum) : 𝓢(Momentum,ℂ) →L[ℂ] ℂ := by
  refine SchwartzMap.mkCLMtoNormedSpace (fun f => f p) (by intros;rfl) (by intros;rfl) ?_
  refine ⟨{(0,0)},1,by norm_num,?_⟩
  intro f
  simpa using SchwartzMap.norm_le_seminorm ℂ f p

@[simp] theorem wick_momentum_evaluation_apply (p : Momentum) (f : 𝓢(Momentum,ℂ)) :
    wickMomentumEvaluation p f=f p := rfl

def wickCovariantDensitySchwartzCLM (a : Parameters) : 𝓢(Momentum,ℂ) →L[ℂ] 𝓢(Momentum,ℂ) :=
  ((1/wickCovariantScale a : ℝ) : ℂ) • wickWignerWeightSchwartzCLM a

/-- Weighted Dirac distribution in ordinary dp coordinates:
2 P0 (2 pi hbar)^3 delta_p. This complex-linear Schwartz distribution
is not yet identified with the Hilbert antidual bra/ket convention. -/
def wickCovariantMomentumDelta (a : Parameters) (p : Momentum) : 𝓢(Momentum,ℂ) →L[ℂ] ℂ :=
  ((2*massShell a p 0*wickSpatialFourierJacobian a : ℝ) : ℂ) • wickMomentumEvaluation p

theorem wick_covariant_density_schwartz_apply (a : Parameters) (f : 𝓢(Momentum,ℂ)) (p : Momentum) :
    wickCovariantDensitySchwartzCLM a f p=
      ((1/(2*massShell a p 0*wickSpatialFourierJacobian a) : ℝ) : ℂ)*f p := by
  change (((1/wickCovariantScale a : ℝ) : ℂ))*(wickWignerWeightSchwartzCLM a f p)=_
  rw [wick_wigner_weight_schwartz_apply]
  have hj : wickSpatialFourierJacobian a≠0 := by
    rw [wick_spatial_fourier_jacobian_value]
    exact pow_ne_zero 3 (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) a.hbar_pos.ne')
  have h : (1/wickCovariantScale a)*wignerWeight a p=
      1/(2*massShell a p 0*wickSpatialFourierJacobian a) := by
    dsimp [wickCovariantScale,wignerWeight,massShell]
    field_simp [a.mass_pos.ne',a.speed_pos.ne',(energy_pos a p).ne',hj]
    <;> ring
  have hc := congrArg Complex.ofReal h
  push_cast at hc
  push_cast
  linear_combination (f p)*hc

/-- Exact weighted-Dirac normalization on every rigging test. No formal
inner product of nonnormalizable vectors is used as an assumption. -/
theorem wick_covariant_momentum_delta_normalization (a : Parameters) (p : Momentum)
    (f : 𝓢(Momentum,ℂ)) :
    wickCovariantMomentumDelta a p (wickCovariantDensitySchwartzCLM a f)=f p := by
  change ((2*massShell a p 0*wickSpatialFourierJacobian a : ℝ) : ℂ)*
    (wickCovariantDensitySchwartzCLM a f p)=_
  rw [wick_covariant_density_schwartz_apply]
  have hp : massShell a p 0≠0 := (div_pos (energy_pos a p) a.speed_pos).ne'
  have hj : wickSpatialFourierJacobian a≠0 := by
    rw [wick_spatial_fourier_jacobian_value]
    exact pow_ne_zero 3 (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) a.hbar_pos.ne')
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hp,Complex.ofReal_ne_zero.mpr hj]

theorem wick_covariant_rigging_unitary_evaluation (a : Parameters) (p : Momentum)
    (f : 𝓢(Momentum,ℂ)) :
    wickMomentumEvaluation p (wickCovariantSchwartz a f)=
      (wickCovariantRoot a : ℂ)*wickMomentumEvaluation p f := rfl

end AASCKleinGordon
