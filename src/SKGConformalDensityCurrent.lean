import SKGStressRegularity

/-! Convert the actual distributional density current to actual covariant
divergence on the constructed metric. This is not a normal-coordinate bridge. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 14000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

theorem same_metric_density_current_covariant (a : Parameters) (T : MetricField)
    (symmetric : MetricFieldSymmetric T) (p : CoordinatePoint)
    (regularT : ∀ i j, DifferentiableAt ℝ (fun x => T x i j) p) (e : Fin 4) :
    classicalTensorDensityCurrent (sourceMetric a) (raisedSourceTensorDensity (sourceMetric a) T) p e =
      sourceFactor a p ^ 2 * coordinateDivergence (sourceMetric a) T p e := by
  have regularL : DifferentiableAt ℝ (sourceFactor a) p :=
    (source_factor_smooth a).differentiable (by simp) p
  have productSame (i j k : Fin 4) :
      (fun x => raisedSourceTensorDensity (sourceMetric a) T x i j * sourceMetric a x j k) =
      fun x => (metric i i * metric j j * metric j k) * (T x i j * sourceFactor a x) := by
    funext x
    rw [same_source_raised_density, source_metric_conformal]
    change (metric i i * metric j j * T x i j) * (sourceFactor a x * metric j k) = _
    ring
  have productPartial (i j k c : Fin 4) :
      scalarPartial (fun x => raisedSourceTensorDensity (sourceMetric a) T x i j * sourceMetric a x j k) p c =
      (metric i i * metric j j * metric j k) *
        (T p i j * scalarPartial (sourceFactor a) p c +
          sourceFactor a p * scalarPartial (fun x => T x i j) p c) := by
    rw [productSame, skg_partial_const_mul _ (fun x => T x i j * sourceFactor a x) p
      ((regularT i j).mul regularL) c,
      skg_partial_mul (fun x => T x i j) (sourceFactor a) p (regularT i j) regularL c]
  have h01 := symmetric p 0 1
  have h02 := symmetric p 0 2
  have h03 := symmetric p 0 3
  have h12 := symmetric p 1 2
  have h13 := symmetric p 1 3
  have h23 := symmetric p 2 3
  unfold classicalTensorDensityCurrent coordinateDivergence coordinateCovariantTensorDerivative
  simp_rw [productPartial, same_source_raised_density, source_metric_conformal,
    scalar_conformal_inverse _ p (source_factor_nonzero a p),
    scalar_conformal_christoffel _ p regularL (source_factor_nonzero a p),
    lowerChristoffel, scalar_conformal_metric_partial _ p regularL]
  fin_cases e <;> simp [metric, Matrix.diagonal_apply, Fin.sum_univ_succ]
  all_goals simp only [h01, h02, h03, h12, h13, h23]
  all_goals field_simp [source_factor_nonzero a p]
  all_goals ring

theorem actual_scalar_source_density_current (a : Parameters) (u : CoordinatePoint → ℝ)
    (regularU : ContDiff ℝ (⊤ : ℕ∞) u) (p : CoordinatePoint) (e : Fin 4) :
    classicalTensorDensityCurrent (sourceMetric a)
      (raisedSourceTensorDensity (sourceMetric a) (sameSourceStress a u)) p e =
      sourceFactor a p ^ 2 *
        ((scalarFieldWaveOperator (sourceMetric a) u p - massWaveNumber a ^ 2 * u p) * scalarPartial u p e) := by
  rw [same_metric_density_current_covariant a _ (same_source_stress_symmetric a u) p
    (fun i j => (same_source_stress_smooth a u regularU i j).differentiable (by simp) p)]
  rw [same_metric_scalar_stress_off_shell a u p
    (regularU.contDiffAt.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) e]

theorem constructed_scalar_source_density_current_zero (a : Parameters) (f h : CurvedCauchyDatum a)
    (p : CoordinatePoint) (inside : p ∈ sourceDomain a) (e : Fin 4) :
    classicalTensorDensityCurrent (sourceMetric a)
      (raisedSourceTensorDensity (sourceMetric a) (sameSourceStress a (sourceField a f h))) p e = 0 := by
  rw [actual_scalar_source_density_current a _ (source_field_smooth a f h) p e,
    source_field_equation a f h p inside, sub_self, zero_mul, mul_zero]

end AASCKleinGordon.SameActionSource
