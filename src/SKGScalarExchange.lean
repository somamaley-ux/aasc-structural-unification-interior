import SKGKineticMassActions

/-! The action sectors exchange the actual mass current. Marginal
conservation is not asserted; only the balanced total is conserved. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

theorem coordinate_divergence_sub (g T S : MetricField) (p : CoordinatePoint)
    (regularT : ∀ a b, DifferentiableAt ℝ (fun q => T q a b) p)
    (regularS : ∀ a b, DifferentiableAt ℝ (fun q => S q a b) p) (b : Fin 4) :
    coordinateDivergence g (T - S) p b =
      coordinateDivergence g T p b - coordinateDivergence g S p b := by
  have derivativePart (c a e : Fin 4) :
      scalarPartial (fun q => T q a e - S q a e) p c =
        scalarPartial (fun q => T q a e) p c - scalarPartial (fun q => S q a e) p c :=
    skg_partial_sub _ _ p (regularT a e) (regularS a e) c
  unfold coordinateDivergence coordinateCovariantTensorDerivative
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  simp only [Pi.sub_apply, Matrix.sub_apply, derivativePart, mul_sub, Finset.sum_sub_distrib]
  ring

theorem kinetic_scalar_stress_smooth (a : Parameters) (u : CoordinatePoint → ℝ)
    (regularU : ContDiff ℝ (⊤ : ℕ∞) u) (i j : Fin 4) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => kineticScalarStress a u p i j) := by
  have same : (fun p => kineticScalarStress a u p i j) =
      fun p => scalarConformalStressPolynomial (sourceFactor a) u 0 p i j := by
    funext p
    rw [kineticScalarStress, source_metric_conformal,
      scalar_conformal_stress_polynomial _ u 0 p (source_factor_nonzero a p)]
  rw [same]
  exact scalar_stress_polynomial_smooth _ u 0 (source_factor_smooth a) regularU i j

def scalarMassExchange (a : Parameters) (u : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (b : Fin 4) : ℝ := massWaveNumber a ^ 2 * u p * scalarPartial u p b

theorem kinetic_scalar_off_shell_balance (a : Parameters) (u : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (regular : ContDiffAt ℝ 2 u p) (b : Fin 4) :
    coordinateDivergence (sourceMetric a) (kineticScalarStress a u) p b =
      scalarFieldWaveOperator (sourceMetric a) u p * scalarPartial u p b := by
  rw [kineticScalarStress, source_metric_conformal,
    scalar_conformal_stress_off_shell _ u 0 (source_factor_nonzero a) p
      ((source_factor_smooth a).differentiable (by simp) p) regular b]
  simp

theorem mass_scalar_actual_balance (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ (⊤ : ℕ∞) u) (p : CoordinatePoint) (b : Fin 4) :
    coordinateDivergence (sourceMetric a) (massScalarStress a u) p b =
      -scalarMassExchange a u p b := by
  have split : massScalarStress a u = sameSourceStress a u - kineticScalarStress a u := by
    rw [scalar_actual_stress_kinetic_mass_split a u]
    abel
  rw [split, coordinate_divergence_sub _ _ _ p
    (fun i j => (same_source_stress_smooth a u regular i j).differentiable (by simp) p)
    (fun i j => (kinetic_scalar_stress_smooth a u regular i j).differentiable (by simp) p) b,
    same_metric_scalar_stress_off_shell a u p
      (regular.contDiffAt.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) b,
    kinetic_scalar_off_shell_balance a u p
      (regular.contDiffAt.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) b]
  unfold scalarMassExchange
  ring

theorem constructed_scalar_opposite_exchange (a : Parameters) (f h : CurvedCauchyDatum a)
    (p : CoordinatePoint) (inside : p ∈ sourceDomain a) (b : Fin 4) :
    coordinateDivergence (sourceMetric a) (kineticScalarStress a (sourceField a f h)) p b =
      scalarMassExchange a (sourceField a f h) p b ∧
    coordinateDivergence (sourceMetric a) (massScalarStress a (sourceField a f h)) p b =
      -scalarMassExchange a (sourceField a f h) p b := by
  constructor
  · rw [kinetic_scalar_off_shell_balance a _ p
      ((source_field_smooth a f h).contDiffAt.of_le
        (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) b,
      source_field_equation a f h p inside]
    rfl
  · exact mass_scalar_actual_balance a _ (source_field_smooth a f h) p b

theorem finite_balanced_exchange_total {A E : Type*} [Fintype A] [Fintype E]
    (D residual external : A → ℝ) (incidence : A → E → ℝ) (current : E → ℝ)
    (sector : ∀ a, D a = residual a + external a + ∑ e, incidence a e * current e)
    (balanced : ∀ e, ∑ a, incidence a e = 0) :
    (∑ a, D a) = (∑ a, residual a) + ∑ a, external a := by
  simp_rw [sector, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, balanced, zero_mul]
  simp

end AASCKleinGordon.SameActionSource
