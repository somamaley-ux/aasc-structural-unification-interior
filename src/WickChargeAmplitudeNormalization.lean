import WickChargeMeasureCoefficient

noncomputable section
set_option maxHeartbeats 1200000
namespace AASCKleinGordon

def wickChargeNormalization (a : Parameters) : ℝ :=
  2*wickSpatialFourierJacobian a*a.mass/a.hbar^2

theorem wick_charge_normalization_positive (a : Parameters) : 0<wickChargeNormalization a := by
  unfold wickChargeNormalization
  rw [wick_spatial_fourier_jacobian_value]
  exact div_pos (mul_pos (mul_pos (by norm_num)
    (pow_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) a.hbar_pos) 3)) a.mass_pos)
      (sq_pos_of_pos a.hbar_pos)

theorem wick_same_tensor_charge_coefficient_real (a : Parameters) (s : ℝ) :
    wickSameTensorChargeCoefficient a s=((wickChargeNormalization a*s^2 : ℝ) : ℂ) := by
  unfold wickSameTensorChargeCoefficient wickChargeNormalization
  push_cast
  ring

theorem wick_same_tensor_charge_coefficient_one_iff (a : Parameters) (s : ℝ) :
    wickSameTensorChargeCoefficient a s=1 ↔ s^2=1/wickChargeNormalization a := by
  rw [wick_same_tensor_charge_coefficient_real,← Complex.ofReal_one,Complex.ofReal_inj]
  have hn := (wick_charge_normalization_positive a).ne'
  constructor
  · intro h
    apply (eq_div_iff hn).mpr
    nlinarith
  · intro h
    have h' := (eq_div_iff hn).mp h
    nlinarith

def wickPositiveCalibratedAmplitude (a : Parameters) : ℝ :=
  Real.sqrt (1/wickChargeNormalization a)

theorem wick_positive_calibrated_amplitude_positive (a : Parameters) :
    0<wickPositiveCalibratedAmplitude a :=
  Real.sqrt_pos.mpr (one_div_pos.mpr (wick_charge_normalization_positive a))

theorem wick_positive_calibrated_amplitude_coefficient (a : Parameters) :
    wickSameTensorChargeCoefficient a (wickPositiveCalibratedAmplitude a)=1 := by
  apply (wick_same_tensor_charge_coefficient_one_iff a _).mpr
  exact Real.sq_sqrt (one_div_pos.mpr (wick_charge_normalization_positive a)).le

theorem wick_same_tensor_zero_amplitude_not_calibrated (a : Parameters) :
    wickSameTensorChargeCoefficient a 0≠1 := by
  simp [wickSameTensorChargeCoefficient]

end AASCKleinGordon
