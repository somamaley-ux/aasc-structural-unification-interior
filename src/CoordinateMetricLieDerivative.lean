import CoordinateCovariantDivergence

/-! The actual coordinate Lie derivative and symmetric covariant gradient.
Metric compatibility is supplied by the previously constructed Levi-Civita
connection, not by an assumed Lie-pairing interface. -/
namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0

def loweredCoordinateVector (g : MetricField) (X : CoordinatePoint → CoordinatePoint)
    (p : CoordinatePoint) (b : Fin 4) : ℝ := ∑ e, g p b e * X p e

def coordinateCovectorDerivative (Γ : ConnectionCoefficients)
    (α : CoordinatePoint → CoordinatePoint) (p : CoordinatePoint) (a b : Fin 4) : ℝ :=
  scalarPartial (fun x => α x b) p a - ∑ e, Γ p e a b * α p e

def coordinateMetricLieDerivative (g : MetricField) (X : CoordinatePoint → CoordinatePoint)
    (p : CoordinatePoint) (a b : Fin 4) : ℝ :=
  ∑ e, (metricPartial g p a b e * X p e +
    g p e b * scalarPartial (fun x => X x e) p a +
    g p a e * scalarPartial (fun x => X x e) p b)

theorem lowered_coordinate_vector_partial (g : MetricField)
    (X : CoordinatePoint → CoordinatePoint) (p : CoordinatePoint)
    (hg : ∀ a b, DifferentiableAt ℝ (fun x => g x a b) p)
    (hX : ∀ a, DifferentiableAt ℝ (fun x => X x a) p) (a b : Fin 4) :
    scalarPartial (fun x => loweredCoordinateVector g X x b) p a =
      ∑ e, (metricPartial g p b e a * X p e +
        g p b e * scalarPartial (fun x => X x e) p a) := by
  have hd := (HasFDerivAt.fun_sum (fun e (_ : e ∈ (Finset.univ : Finset (Fin 4))) =>
    (hg b e).hasFDerivAt.mul (hX e).hasFDerivAt)).fderiv
  change fderiv ℝ (fun x => loweredCoordinateVector g X x b) p = _ at hd
  simp only [scalarPartial, hd, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, metricPartial]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem leviCivita_symmetric_lowering_identity (g : MetricField)
    (symmetric : MetricFieldSymmetric g) (p : CoordinatePoint)
    (nondegenerate : (g p).det ≠ 0) (a b e : Fin 4) :
    metricPartial g p b e a + metricPartial g p a e b -
      2 * (∑ r : Fin 4, leviCivitaCoefficients g p r a b * g p r e) =
        metricPartial g p a b e := by
  have low := leviCivita_lowering g p nondegenerate e a b
  have hs : (∑ r : Fin 4, leviCivitaCoefficients g p r a b * g p r e) =
      lowerChristoffel g p e a b := by
    rw [← low]
    apply Finset.sum_congr rfl
    intro r _
    rw [symmetric p r e]
    ring
  rw [hs]
  unfold lowerChristoffel
  rw [metricPartial_symmetric g symmetric p e b a,
    metricPartial_symmetric g symmetric p e a b]
  ring

theorem coordinate_metric_lie_eq_symmetric_covariant_gradient
    (g : MetricField) (X : CoordinatePoint → CoordinatePoint) (p : CoordinatePoint)
    (symmetric : MetricFieldSymmetric g) (nondegenerate : (g p).det ≠ 0)
    (hg : ∀ a b, DifferentiableAt ℝ (fun x => g x a b) p)
    (hX : ∀ a, DifferentiableAt ℝ (fun x => X x a) p) (a b : Fin 4) :
    coordinateMetricLieDerivative g X p a b =
      coordinateCovectorDerivative (leviCivitaCoefficients g) (loweredCoordinateVector g X) p a b +
      coordinateCovectorDerivative (leviCivitaCoefficients g) (loweredCoordinateVector g X) p b a := by
  unfold coordinateCovectorDerivative
  rw [lowered_coordinate_vector_partial g X p hg hX a b,
    lowered_coordinate_vector_partial g X p hg hX b a]
  have expand (a b : Fin 4) :
      (∑ r : Fin 4, leviCivitaCoefficients g p r a b * loweredCoordinateVector g X p r) =
        ∑ e : Fin 4, (∑ r : Fin 4, leviCivitaCoefficients g p r a b * g p r e) * X p e := by
    simp only [loweredCoordinateVector, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul, mul_assoc]
  rw [expand a b, expand b a]
  simp_rw [leviCivita_torsion_free g symmetric p _ b a]
  unfold coordinateMetricLieDerivative
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hs := leviCivita_symmetric_lowering_identity g symmetric p nondegenerate a b e
  rw [symmetric p e b]
  rw [← hs]
  ring

#print axioms lowered_coordinate_vector_partial
#print axioms leviCivita_symmetric_lowering_identity
#print axioms coordinate_metric_lie_eq_symmetric_covariant_gradient
end
end AASCSemanticExhaustion
