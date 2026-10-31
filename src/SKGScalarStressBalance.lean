import SKGScalarStressDerivative
import SKGSameMetricRegularity

/-! Actual off-shell covariant stress balance and on-shell conservation on
the very same admitted Stage1 metric. No conservation certificate is input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

theorem scalar_conformal_actual_stress_partial (L u : CoordinatePoint → ℝ) (mu2 : ℝ)
    (nonzero : ∀ p, L p ≠ 0) (p : CoordinatePoint)
    (regularL : DifferentiableAt ℝ L p) (regularU : ContDiffAt ℝ 2 u p) (c a b : Fin 4) :
    scalarPartial (fun x => scalarFieldStress (scalarConformalMetric L) u mu2 x a b) p c =
      scalarStressJetPartial (L p) (u p) mu2 (scalarPartial u p) (scalarPartial L p)
        (scalarSecondPartial u p) c a b := by
  have same : scalarFieldStress (scalarConformalMetric L) u mu2 =
      scalarConformalStressPolynomial L u mu2 :=
    funext (fun x => scalar_conformal_stress_polynomial L u mu2 x (nonzero x))
  rw [same]
  exact scalar_stress_polynomial_partial L u mu2 p regularL regularU c a b

theorem scalar_conformal_actual_divergence_as_jet (L u : CoordinatePoint → ℝ) (mu2 : ℝ)
    (nonzero : ∀ p, L p ≠ 0) (p : CoordinatePoint)
    (regularL : DifferentiableAt ℝ L p) (regularU : ContDiffAt ℝ 2 u p) (b : Fin 4) :
    coordinateDivergence (scalarConformalMetric L)
      (scalarFieldStress (scalarConformalMetric L) u mu2) p b =
      scalarStressJetDivergence (L p) (u p) mu2 (scalarPartial u p) (scalarPartial L p)
        (scalarSecondPartial u p) b := by
  have value (a e : Fin 4) : scalarFieldStress (scalarConformalMetric L) u mu2 p a e =
      scalarStressJetValue (L p) (u p) mu2 (scalarPartial u p) a e := by
    rw [scalar_conformal_stress_polynomial L u mu2 p (nonzero p)]
    rfl
  unfold coordinateDivergence coordinateCovariantTensorDerivative
  simp_rw [scalar_conformal_inverse L p (nonzero p),
    scalar_conformal_actual_stress_partial L u mu2 nonzero p regularL regularU,
    scalar_conformal_christoffel L p regularL (nonzero p), value]
  change (∑ a : Fin 4, ∑ c : Fin 4, (L p)⁻¹ * metric a c *
    (scalarStressJetPartial (L p) (u p) mu2 (scalarPartial u p) (scalarPartial L p)
        (scalarSecondPartial u p) c a b -
      (∑ e : Fin 4, scalarConformalConnectionJet (L p) (scalarPartial L p) e c a *
        scalarStressJetValue (L p) (u p) mu2 (scalarPartial u p) e b) -
      (∑ e : Fin 4, scalarConformalConnectionJet (L p) (scalarPartial L p) e c b *
        scalarStressJetValue (L p) (u p) mu2 (scalarPartial u p) a e))) = _
  simp only [scalarStressJetDivergence]
  have diagonal := canonical_metric_contraction_diagonal (fun a c =>
    scalarStressJetPartial (L p) (u p) mu2 (scalarPartial u p) (scalarPartial L p)
        (scalarSecondPartial u p) c a b -
      (∑ e : Fin 4, scalarConformalConnectionJet (L p) (scalarPartial L p) e c a *
        scalarStressJetValue (L p) (u p) mu2 (scalarPartial u p) e b) -
      (∑ e : Fin 4, scalarConformalConnectionJet (L p) (scalarPartial L p) e c b *
        scalarStressJetValue (L p) (u p) mu2 (scalarPartial u p) a e))
  simpa only [Finset.mul_sum, mul_assoc] using
    congrArg (fun r : ℝ => (L p)⁻¹ * r) diagonal

theorem scalar_conformal_stress_off_shell (L u : CoordinatePoint → ℝ) (mu2 : ℝ)
    (nonzero : ∀ p, L p ≠ 0) (p : CoordinatePoint)
    (regularL : DifferentiableAt ℝ L p) (regularU : ContDiffAt ℝ 2 u p) (b : Fin 4) :
    coordinateDivergence (scalarConformalMetric L)
      (scalarFieldStress (scalarConformalMetric L) u mu2) p b =
      (scalarFieldWaveOperator (scalarConformalMetric L) u p - mu2 * u p) * scalarPartial u p b := by
  rw [scalar_conformal_actual_divergence_as_jet L u mu2 nonzero p regularL regularU,
    scalar_conformal_wave_operator L u p regularL (nonzero p)]
  exact scalar_stress_off_shell_jet_algebra (L p) (u p) mu2 (scalarPartial u p)
    (scalarPartial L p) (scalarSecondPartial u p) (nonzero p)
    (c2_scalarSecondPartial_symmetric u p regularU) b

theorem same_metric_scalar_stress_off_shell (a : Parameters) (u : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (regularU : ContDiffAt ℝ 2 u p) (b : Fin 4) :
    coordinateDivergence (sourceMetric a) (scalarFieldStress (sourceMetric a) u (massWaveNumber a ^ 2)) p b =
      (scalarFieldWaveOperator (sourceMetric a) u p - massWaveNumber a ^ 2 * u p) * scalarPartial u p b := by
  rw [source_metric_conformal]
  exact scalar_conformal_stress_off_shell _ u _ (source_factor_nonzero a) p
    ((source_factor_smooth a).differentiable (by simp) p) regularU b

theorem constructed_scalar_stress_conserved (a : Parameters) (f h : CurvedCauchyDatum a)
    (p : CoordinatePoint) (inside : p ∈ sourceDomain a) :
    coordinateDivergence (sourceMetric a)
      (scalarFieldStress (sourceMetric a) (sourceField a f h) (massWaveNumber a ^ 2)) p = 0 := by
  funext b
  have regularU : ContDiffAt ℝ 2 (sourceField a f h) p :=
    (source_field_smooth a f h).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  rw [same_metric_scalar_stress_off_shell a _ p
    regularU b,
    source_field_equation a f h p inside, sub_self, zero_mul]
  rfl

end AASCKleinGordon.SameActionSource
