import SKGActualMatterSource

/-! Smoothness and the actual raised tensor density, globally for the
constructed positive conformal operand. No smooth-density certificate input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

abbrev sameSourceStress (a : Parameters) (u : CoordinatePoint → ℝ) : MetricField :=
  scalarFieldStress (sourceMetric a) u (massWaveNumber a ^ 2)

theorem same_source_stress_symmetric (a : Parameters) (u : CoordinatePoint → ℝ) :
    MetricFieldSymmetric (sameSourceStress a u) := by
  intro p i j
  simp only [sameSourceStress, scalarFieldStress]
  rw [source_metric_symmetric a p i j]
  ring

theorem scalar_stress_polynomial_smooth (L u : CoordinatePoint → ℝ) (mu2 : ℝ)
    (regularL : ContDiff ℝ (⊤ : ℕ∞) L) (regularU : ContDiff ℝ (⊤ : ℕ∞) u) (a b : Fin 4) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => scalarConformalStressPolynomial L u mu2 p a b) := by
  have hP (i : Fin 4) := scalar_partial_smooth u regularU i
  have hK : ContDiff ℝ (⊤ : ℕ∞) (fun p => scalarFlatKinetic (scalarPartial u p)) := by
    exact ContDiff.sum (fun i _ => contDiff_const.mul ((hP i).pow 2))
  exact ((hP a).mul (hP b)).sub (contDiff_const.mul
    (hK.add ((contDiff_const.mul regularL).mul (regularU.pow 2))))

theorem same_source_stress_smooth (a : Parameters) (u : CoordinatePoint → ℝ)
    (regularU : ContDiff ℝ (⊤ : ℕ∞) u) (i j : Fin 4) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => sameSourceStress a u p i j) := by
  have same : (fun p => sameSourceStress a u p i j) =
      fun p => scalarConformalStressPolynomial (sourceFactor a) u (massWaveNumber a ^ 2) p i j := by
    funext p
    rw [sameSourceStress, source_metric_conformal,
      scalar_conformal_stress_polynomial _ u _ p (source_factor_nonzero a p)]
  rw [same]
  exact scalar_stress_polynomial_smooth _ u _ (source_factor_smooth a) regularU i j

theorem scalar_conformal_raised_density (L : CoordinatePoint → ℝ) (T : MetricField)
    (p : CoordinatePoint) (nonzero : L p ≠ 0) (a b : Fin 4) :
    raisedSourceTensorDensity (scalarConformalMetric L) T p a b =
      metric a a * metric b b * T p a b := by
  simp only [raisedSourceTensorDensity, scalar_conformal_coordinate_volume,
    scalar_conformal_inverse L p nonzero]
  fin_cases a <;> fin_cases b <;>
    simp [metric, Matrix.diagonal_apply, Fin.sum_univ_succ]
  all_goals field_simp [nonzero]
  all_goals ring

theorem same_source_raised_density (a : Parameters) (T : MetricField)
    (p : CoordinatePoint) (i j : Fin 4) :
    raisedSourceTensorDensity (sourceMetric a) T p i j = metric i i * metric j j * T p i j := by
  rw [source_metric_conformal]
  exact scalar_conformal_raised_density _ T p (source_factor_nonzero a p) i j

def actualSourceDensityCoordinates (a : Parameters) (u : CoordinatePoint → ℝ)
    (i : Fin 10) (p : CoordinatePoint) : ℝ :=
  sourceDensityCoordinates (raisedSourceTensorDensity (sourceMetric a) (sameSourceStress a u)) i p

theorem actual_source_density_smooth (a : Parameters) (u : CoordinatePoint → ℝ)
    (regularU : ContDiff ℝ (⊤ : ℕ∞) u) (i : Fin 10) :
    ContDiff ℝ (⊤ : ℕ∞) (actualSourceDensityCoordinates a u i) := by
  have same : actualSourceDensityCoordinates a u i = fun p =>
      (metric (sourceSymmetricPair i).1 (sourceSymmetricPair i).1 *
       metric (sourceSymmetricPair i).2 (sourceSymmetricPair i).2) *
        sameSourceStress a u p (sourceSymmetricPair i).1 (sourceSymmetricPair i).2 := by
    funext p
    exact same_source_raised_density a _ p _ _
  rw [same]
  exact contDiff_const.mul (same_source_stress_smooth a u regularU _ _)

end AASCKleinGordon.SameActionSource
