import EHKGCompactConformalOperand
import ScalarFieldSourceBalance

/-! Actual matrix inverse and Levi-Civita scalar operator of a time-dependent
conformal metric. Derivative hypotheses concern the displayed scalar function,
not a stipulated PDE, propagator, or interpretation bridge. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology BigOperators
namespace AASCKleinGordon.CurvedKG

def timeConformalMetric (A : ℝ → ℝ) : MetricField := fun p => (A (p 0)) ^ 2 • metric

theorem time_conformal_inverse (A : ℝ → ℝ) (p : CoordinatePoint) (nonzero : A (p 0) ≠ 0) :
    (timeConformalMetric A p)⁻¹ = ((A (p 0)) ^ 2)⁻¹ • metric := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [timeConformalMetric, Matrix.mul_apply, Fin.sum_univ_succ, metric,
      Matrix.diagonal_apply, nonzero]

theorem time_conformal_metric_partial (A : ℝ → ℝ) (p : CoordinatePoint) (q : ℝ)
    (derivative : HasDerivAt A q (p 0)) (i j c : Fin 4) :
    metricPartial (timeConformalMetric A) p i j c =
      2 * A (p 0) * q * (if c = 0 then 1 else 0) * metric i j := by
  have first := derivative.comp_hasFDerivAt p
    (ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt (fun x : CoordinatePoint => A (x 0))
    (q • (ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ)) p at first
  change fderiv ℝ (fun x : CoordinatePoint => A (x 0) ^ 2 * metric i j) p (Pi.single c 1) = _
  rw [((first.pow 2).mul_const (metric i j)).fderiv]
  simp [Pi.single_apply, eq_comm]
  <;> ring

theorem time_conformal_christoffel (A : ℝ → ℝ) (p : CoordinatePoint) (q : ℝ)
    (derivative : HasDerivAt A q (p 0)) (nonzero : A (p 0) ≠ 0) (e b c : Fin 4) :
    leviCivitaCoefficients (timeConformalMetric A) p e b c =
      (q / A (p 0)) *
        ((if e = b ∧ c = 0 then 1 else 0) +
         (if e = c ∧ b = 0 then 1 else 0) +
         metric b c * (if e = 0 then 1 else 0)) := by
  simp only [leviCivitaCoefficients, time_conformal_inverse A p nonzero, lowerChristoffel,
    time_conformal_metric_partial A p q derivative]
  fin_cases e <;> fin_cases b <;> fin_cases c <;>
    simp [metric, Matrix.diagonal_apply, Fin.sum_univ_succ]
  all_goals field_simp
  all_goals ring

theorem time_conformal_scalar_wave_operator (A : ℝ → ℝ) (p : CoordinatePoint) (q : ℝ)
    (derivative : HasDerivAt A q (p 0)) (nonzero : A (p 0) ≠ 0)
    (u : CoordinatePoint → ℝ) :
    scalarFieldWaveOperator (timeConformalMetric A) u p =
      ((A (p 0)) ^ 2)⁻¹ *
        (-scalarSecondPartial u p 0 0 + scalarSecondPartial u p 1 1 +
          scalarSecondPartial u p 2 2 + scalarSecondPartial u p 3 3 -
          2 * q / A (p 0) * scalarPartial u p 0) := by
  simp only [scalarFieldWaveOperator, time_conformal_inverse A p nonzero,
    time_conformal_christoffel A p q derivative nonzero]
  simp [metric, Matrix.diagonal_apply, Fin.sum_univ_succ]
  ring

/-- Algebra used after the actual quotient derivatives have been computed. -/
theorem conformal_rescaling_residual_algebra
    (A q r mu2 nu2 v vt vtt lap : ℝ) (nonzero : A ≠ 0)
    (mass : mu2 = 2 * nu2) (acceleration : r = nu2 * (2 * A ^ 3 - A)) :
    (A ^ 2)⁻¹ *
      (-(vtt / A - 2 * q * vt / A ^ 2 - r * v / A ^ 2 + 2 * q ^ 2 * v / A ^ 3)
        + lap / A - 2 * q / A * (vt / A - q * v / A ^ 2)) - mu2 * (v / A) =
      -(A ^ 3)⁻¹ * (vtt - lap + nu2 * v) := by
  rw [mass, acceleration]
  field_simp
  <;> ring

end AASCKleinGordon.CurvedKG
