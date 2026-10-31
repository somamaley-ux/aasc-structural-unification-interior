import CoordinateCovariantDivergence

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0
set_option autoImplicit false

def differentiableTensorGerms : Submodule ℝ MetricField where
  carrier := {T | ∀ a b, DifferentiableAt ℝ (fun x => T x a b) 0}
  zero_mem' := by intro a b; exact differentiableAt_const _
  add_mem' := by
    intro T U hT hU a b
    exact (hT a b).add (hU a b)
  smul_mem' := by
    intro r T hT a b
    exact (hT a b).const_smul r

theorem scalarPartial_add_at_zero (f h : CoordinatePoint → ℝ)
    (hf : DifferentiableAt ℝ f 0) (hh : DifferentiableAt ℝ h 0) (c : Fin 4) :
    scalarPartial (fun x => f x + h x) 0 c = scalarPartial f 0 c + scalarPartial h 0 c := by
  have hd := (hf.hasFDerivAt.add hh.hasFDerivAt).fderiv
  change fderiv ℝ (fun x => f x + h x) 0 = _ at hd
  simp only [scalarPartial, hd, ContinuousLinearMap.add_apply]

theorem scalarPartial_smul_at_zero (r : ℝ) (f : CoordinatePoint → ℝ)
    (hf : DifferentiableAt ℝ f 0) (c : Fin 4) :
    scalarPartial (fun x => r * f x) 0 c = r * scalarPartial f 0 c := by
  have hd := (hf.hasFDerivAt.const_mul r).fderiv
  change fderiv ℝ (fun x => r * f x) 0 = _ at hd
  simp only [scalarPartial, hd, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem coordinateDivergence_add_at_zero (g T U : MetricField)
    (hT : ∀ a b, DifferentiableAt ℝ (fun x => T x a b) 0)
    (hU : ∀ a b, DifferentiableAt ℝ (fun x => U x a b) 0) :
    coordinateDivergence g (T + U) 0 = coordinateDivergence g T 0 + coordinateDivergence g U 0 := by
  funext b
  simp only [coordinateDivergence, coordinateCovariantTensorDerivative,
    Pi.add_apply, Matrix.add_apply]
  simp_rw [scalarPartial_add_at_zero _ _ (hT _ _) (hU _ _)]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

theorem coordinateDivergence_smul_at_zero (g T : MetricField) (r : ℝ)
    (hT : ∀ a b, DifferentiableAt ℝ (fun x => T x a b) 0) :
    coordinateDivergence g (r • T) 0 = r • coordinateDivergence g T 0 := by
  funext b
  simp only [coordinateDivergence, coordinateCovariantTensorDerivative,
    Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [scalarPartial_smul_at_zero r _ (hT _ _)]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  simp only [← mul_assoc]
  have hc (x y : ℝ) : x * r * y = r * x * y := by ring
  simp_rw [hc]
  ring

/-- Actual covariant divergence is linear on differentiable tensor germs.
No linearity on all nondifferentiable functions is postulated. -/
def coordinateDivergenceLinear (g : MetricField) : differentiableTensorGerms →ₗ[ℝ] CoordinatePoint where
  toFun T := coordinateDivergence g T 0
  map_add' T U := coordinateDivergence_add_at_zero g T U T.property U.property
  map_smul' r T := coordinateDivergence_smul_at_zero g T r T.property

def metricTensorGerm (g : MetricField) (germ : C3NormalizedMetricGerm g) : differentiableTensorGerms :=
  ⟨g, fun a b => (germ.2.1 a b).differentiableAt (by norm_num)⟩

def ricciTensorGerm (g : MetricField) (germ : C3NormalizedMetricGerm g) : differentiableTensorGerms :=
  ⟨coordinateRicci g, fun a b => (c3_normal_coordinateRicci_hasFDerivAt g germ a b).differentiableAt⟩

def scalarMetricTensorGerm (g : MetricField) (germ : C3NormalizedMetricGerm g) : differentiableTensorGerms :=
  ⟨coordinateScalarMetric g, fun a b =>
    ((c3_normal_coordinateScalar_hasFDerivAt g germ).mul
      ((germ.2.1 a b).differentiableAt (by norm_num)).hasFDerivAt).differentiableAt⟩

#print axioms scalarPartial_add_at_zero
#print axioms scalarPartial_smul_at_zero
#print axioms coordinateDivergence_add_at_zero
#print axioms coordinateDivergence_smul_at_zero
end
end AASCSemanticExhaustion
