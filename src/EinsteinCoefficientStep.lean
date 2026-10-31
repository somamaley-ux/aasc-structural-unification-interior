import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-!
One component of the requested Einstein normal-form proof, not a metric
construction or the full SameScopeMetric1 theorem. The geometric identities,
existence of the projection, and curvature-response exhaustion are explicit
external obligations. In particular this file does not derive Bianchi or Ward
identities by calling their conclusion admissibility.
-/

namespace MetricProjectionAudit

variable {V W : Type*}
variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup W] [Module ℝ W]

def response (ricci traceMetric metric : V) (a b c : ℝ) : V :=
  a • ricci + b • traceMetric + c • metric

/-- Contracted Bianchi, the trace product identity and metric compatibility
give the divergence calculation. These identities remain explicit premises. -/
theorem divergence_response
    (D : V →ₗ[ℝ] W) (ricci traceMetric metric : V) (gradient : W)
    (bianchi : D ricci = (1 / 2 : ℝ) • gradient)
    (trace_derivative : D traceMetric = gradient)
    (metric_compatible : D metric = 0) (a b c : ℝ) :
    D (response ricci traceMetric metric a b c) =
      (a / 2 + b) • gradient := by
  rw [response, map_add, map_add, map_smul, map_smul, map_smul,
    bianchi, trace_derivative, metric_compatible]
  module

/-- The nonzero gradient condition is essential: it may be supplied by one
member of a universal comparison family, but not inferred for a fixed flat or
constant-scalar-curvature background. -/
theorem coefficient_lock_iff
    (D : V →ₗ[ℝ] W) (ricci traceMetric metric : V) (gradient : W)
    (bianchi : D ricci = (1 / 2 : ℝ) • gradient)
    (trace_derivative : D traceMetric = gradient)
    (metric_compatible : D metric = 0) (gradient_nonzero : gradient ≠ 0)
    (a b c : ℝ) :
    D (response ricci traceMetric metric a b c) = 0 ↔ b = -a / 2 := by
  rw [divergence_response D ricci traceMetric metric gradient
    bianchi trace_derivative metric_compatible]
  constructor
  · intro h
    have hc : a / 2 + b = 0 := (smul_eq_zero.mp h).resolve_right gradient_nonzero
    linarith
  · intro h
    have hc : a / 2 + b = 0 := by linarith
    rw [hc, zero_smul]

/-- Once coefficient locking is proved, the response has Einstein combination
form. No claim of uniqueness of the metric or of the coefficients is made. -/
theorem einstein_combination
    (ricci traceMetric metric : V) (a b c : ℝ) (hb : b = -a / 2) :
    response ricci traceMetric metric a b c =
      a • (ricci - (1 / 2 : ℝ) • traceMetric) + c • metric := by
  rw [hb, response]
  module

/-- A constant-curvature-gradient background alone cannot force the ratio.
This is a concrete nonempty scalar linear-algebra example, not a geometric
counterexample to the manuscript's universal comparison-class claim. -/
theorem zero_gradient_does_not_lock_coefficients :
    ∃ (D : ℝ →ₗ[ℝ] ℝ) (r t g a b c : ℝ),
      D r = (1 / 2 : ℝ) * 0 ∧ D t = 0 ∧ D g = 0 ∧
      D (response r t g a b c) = 0 ∧ b ≠ -a / 2 := by
  refine ⟨0, 0, 0, 1, 0, 1, 1, ?_⟩
  norm_num

#print axioms divergence_response
#print axioms coefficient_lock_iff
#print axioms einstein_combination
#print axioms zero_gradient_does_not_lock_coefficients

end MetricProjectionAudit
