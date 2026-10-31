import EHKGCommonActionAxes
import NativeClockHilbertSourceComponents

/-! Actual conformal metric calculations in four coordinates. The factor may
depend on every coordinate. No normal-coordinate or covariance bridge is an
input. This module has no field equation or source matching hypothesis. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

def scalarConformalMetric (L : CoordinatePoint → ℝ) : MetricField :=
  fun p => L p • metric

theorem scalar_conformal_symmetric (L : CoordinatePoint → ℝ) :
    MetricFieldSymmetric (scalarConformalMetric L) := by
  intro p a b
  fin_cases a <;> fin_cases b <;> rfl

theorem scalar_conformal_inverse (L : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (nonzero : L p ≠ 0) :
    (scalarConformalMetric L p)⁻¹ = (L p)⁻¹ • metric := by
  apply Matrix.inv_eq_left_inv
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [scalarConformalMetric, Matrix.mul_apply, Fin.sum_univ_succ,
      metric, Matrix.diagonal_apply, nonzero]

theorem scalar_conformal_determinant (L : CoordinatePoint → ℝ) (p : CoordinatePoint) :
    (scalarConformalMetric L p).det = -(L p) ^ 4 := by
  rw [scalarConformalMetric, Matrix.det_smul]
  norm_num [metric, Matrix.det_diagonal, Fin.prod_univ_succ]

theorem scalar_conformal_native_volume (L : CoordinatePoint → ℝ) (p : CoordinatePoint) :
    nativeRealClockVolume (scalarConformalMetric L p) = (L p) ^ 2 := by
  rw [nativeRealClockVolume, scalar_conformal_determinant, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ (L p) ^ 4)]
  rw [show (L p) ^ 4 = ((L p) ^ 2) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (L p) ^ 2)]

theorem scalar_conformal_coordinate_volume (L : CoordinatePoint → ℝ) (p : CoordinatePoint) :
    coordinateVolumeDensity (scalarConformalMetric L) p = (L p) ^ 2 := by
  rw [coordinateVolumeDensity, scalar_conformal_determinant, neg_neg]
  rw [show (L p) ^ 4 = ((L p) ^ 2) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (L p) ^ 2)]

theorem scalar_conformal_metric_partial (L : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (regular : DifferentiableAt ℝ L p) (a b c : Fin 4) :
    metricPartial (scalarConformalMetric L) p a b c =
      scalarPartial L p c * metric a b := by
  change fderiv ℝ (fun x => L x * metric a b) p (Pi.single c 1) = _
  rw [(regular.hasFDerivAt.mul_const (metric a b)).fderiv]
  simp [scalarPartial, mul_comm]

theorem scalar_conformal_christoffel (L : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (regular : DifferentiableAt ℝ L p) (nonzero : L p ≠ 0) (e b c : Fin 4) :
    leviCivitaCoefficients (scalarConformalMetric L) p e b c =
      (1 / 2 : ℝ) * (L p)⁻¹ *
        ((if e = b then scalarPartial L p c else 0) +
         (if e = c then scalarPartial L p b else 0) -
         metric b c * metric e e * scalarPartial L p e) := by
  simp only [leviCivitaCoefficients, scalar_conformal_inverse L p nonzero,
    lowerChristoffel, scalar_conformal_metric_partial L p regular]
  fin_cases e <;> fin_cases b <;> fin_cases c <;>
    simp [metric, Matrix.diagonal_apply, Fin.sum_univ_succ] <;> ring

def scalarFlatKinetic (P : Fin 4 → ℝ) : ℝ := ∑ i : Fin 4, metric i i * P i ^ 2

theorem scalar_flat_kinetic_contraction (P : Fin 4 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4, metric i j * P i * P j) = scalarFlatKinetic P := by
  simp_rw [mul_assoc]
  rw [canonical_metric_contraction_diagonal]
  simp only [scalarFlatKinetic, pow_two, mul_assoc]

theorem scalar_conformal_kinetic (L : CoordinatePoint → ℝ) (u : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (nonzero : L p ≠ 0) :
    scalarFieldKinetic (scalarConformalMetric L) u p =
      (L p)⁻¹ * scalarFlatKinetic (scalarPartial u p) := by
  rw [scalarFieldKinetic, scalar_conformal_inverse L p nonzero]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [← scalar_flat_kinetic_contraction (scalarPartial u p)]
  simp only [Finset.mul_sum, mul_assoc]

def scalarConformalStressPolynomial (L : CoordinatePoint → ℝ) (u : CoordinatePoint → ℝ)
    (mu2 : ℝ) : MetricField := fun p a b =>
  scalarPartial u p a * scalarPartial u p b - (1 / 2 : ℝ) * metric a b *
    (scalarFlatKinetic (scalarPartial u p) + mu2 * L p * u p ^ 2)

theorem scalar_conformal_stress_polynomial (L : CoordinatePoint → ℝ)
    (u : CoordinatePoint → ℝ) (mu2 : ℝ) (p : CoordinatePoint) (nonzero : L p ≠ 0) :
    scalarFieldStress (scalarConformalMetric L) u mu2 p =
      scalarConformalStressPolynomial L u mu2 p := by
  ext a b
  rw [scalarFieldStress, scalar_conformal_kinetic L u p nonzero]
  change _ = scalarPartial u p a * scalarPartial u p b - (1 / 2 : ℝ) * metric a b *
    (scalarFlatKinetic (scalarPartial u p) + mu2 * L p * u p ^ 2)
  simp only [scalarConformalMetric, Matrix.smul_apply, smul_eq_mul]
  field_simp [nonzero]
  <;> ring

theorem scalar_conformal_wave_operator (L : CoordinatePoint → ℝ) (u : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (regular : DifferentiableAt ℝ L p) (nonzero : L p ≠ 0) :
    scalarFieldWaveOperator (scalarConformalMetric L) u p =
      (L p)⁻¹ * (∑ i : Fin 4, metric i i * scalarSecondPartial u p i i) +
      (L p)⁻¹ ^ 2 * (∑ i : Fin 4, metric i i * scalarPartial L p i * scalarPartial u p i) := by
  simp only [scalarFieldWaveOperator, scalar_conformal_inverse L p nonzero,
    scalar_conformal_christoffel L p regular nonzero]
  simp [metric, Matrix.diagonal_apply, Fin.sum_univ_succ]
  ring

theorem same_eh_metric_is_scalar_conformal (a : Parameters) :
    originalEHActMetric (conformalOperand (conformalFrequency a)) =
      scalarConformalMetric (conformalMetricFactor (conformalFrequency a)) := by
  funext p
  exact conformal_operand_actual_metric _ p

end AASCKleinGordon.SameActionSource
