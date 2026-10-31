import NativeRealClockHilbertDerivative

/-! Explicit finite-jet-to-analysis audit: the already constructed dual-number
clock action jet is exactly the value/ordinary-real-derivative pair. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open scoped BigOperators

theorem native_trace_pairing_symmetric (A H : NativeRealMatrix) (hs : A.transpose=A) :
    Matrix.trace (A*H)=∑ a,∑ b,A a b*H a b := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hh:=congrArg (fun M : NativeRealMatrix => M a b) hs
  simpa only [Matrix.transpose_apply] using congrArg (fun r : ℝ => r*H a b) hh

theorem native_clock_normal_metric_square : nativeClockNormalMetric*nativeClockNormalMetric=1 := by
  rw [native_clock_normal_metric_eq_canonical,canonical_metric_square]

theorem native_clock_normal_metric_inverse : nativeClockNormalMetric⁻¹=nativeClockNormalMetric :=
  Matrix.inv_eq_right_inv native_clock_normal_metric_square

theorem native_clock_normal_volume : nativeRealClockVolume nativeClockNormalMetric=1 := by
  simp [nativeRealClockVolume,native_clock_normal_metric_eq_canonical,canonical_lorentz_metric_det]

theorem native_real_clock_normal_stress (v : Fin 4 → ℝ) (φ μ : ℝ) :
    nativeRealClockStress nativeClockNormalMetric v φ μ=nativeClockHilbertStress v φ μ := by
  ext a b
  simp [nativeRealClockStress,nativeRealClockOuter,nativeRealClockQuadratic,
    nativeClockHilbertStress,native_clock_normal_metric_inverse]
  ring

theorem native_clock_raised_normal_stress_symmetric (v : Fin 4 → ℝ) (φ μ : ℝ) :
    (nativeClockNormalMetric*nativeClockHilbertStress v φ μ*nativeClockNormalMetric).transpose=
      nativeClockNormalMetric*nativeClockHilbertStress v φ μ*nativeClockNormalMetric := by
  have hη : nativeClockNormalMetric.transpose=nativeClockNormalMetric := by
    simp [nativeClockNormalMetric]
  have hT : (nativeClockHilbertStress v φ μ).transpose=nativeClockHilbertStress v φ μ := by
    ext a b
    have hh:=congrArg (fun M : NativeRealMatrix => M a b) hη
    simp only [Matrix.transpose_apply] at hh
    simp only [Matrix.transpose_apply,nativeClockHilbertStress,hh]
    ring
  rw [Matrix.transpose_mul,Matrix.transpose_mul,hη,hT]
  simp only [Matrix.mul_assoc]

theorem native_real_clock_derivative_equals_constructed_jet (H : NativeRealMatrix)
    (v : Fin 4 → ℝ) (φ μ : ℝ) :
    HasDerivAt (fun s : ℝ => nativeRealClockDensity (nativeClockNormalMetric+s • H) v φ μ)
      (nativeClockLagrangianMetricJet H v φ μ).snd 0 := by
  have hn : nativeClockNormalMetric.det≠0 := by
    rw [native_clock_normal_metric_eq_canonical,canonical_lorentz_metric_det]
    norm_num
  have hd:=native_real_clock_hilbert_density_hasDerivAt nativeClockNormalMetric H hn v φ μ
  rw [native_clock_normal_metric_inverse,native_real_clock_normal_stress,native_clock_normal_volume,
    native_trace_pairing_symmetric _ H (native_clock_raised_normal_stress_symmetric v φ μ)] at hd
  rw [native_clock_actual_metric_lagrangian_coefficient]
  simpa using hd

def nativeOrdinaryRealFirstJet (f : ℝ → ℝ) : DualNumber ℝ := ⟨f 0,deriv f 0⟩

theorem native_clock_finite_jet_is_ordinary_real_jet (H : NativeRealMatrix)
    (v : Fin 4 → ℝ) (φ μ : ℝ) :
    nativeOrdinaryRealFirstJet (fun s : ℝ => nativeRealClockDensity (nativeClockNormalMetric+s • H) v φ μ)=
      nativeClockLagrangianMetricJet H v φ μ := by
  apply TrivSqZeroExt.ext
  · simp [nativeOrdinaryRealFirstJet,nativeRealClockDensity,native_clock_normal_volume,
      native_clock_normal_metric_inverse,nativeClockLagrangianMetricJet,nativeClockVolumeJet,
      nativeClockInverseJet,TrivSqZeroExt.fst_sum,mul_assoc]
  · exact (native_real_clock_derivative_equals_constructed_jet H v φ μ).deriv

#print axioms native_trace_pairing_symmetric
#print axioms native_clock_normal_metric_square
#print axioms native_clock_normal_metric_inverse
#print axioms native_clock_normal_volume
#print axioms native_real_clock_normal_stress
#print axioms native_clock_raised_normal_stress_symmetric
#print axioms native_real_clock_derivative_equals_constructed_jet
#print axioms native_clock_finite_jet_is_ordinary_real_jet
end
end AASCSemanticExhaustion
