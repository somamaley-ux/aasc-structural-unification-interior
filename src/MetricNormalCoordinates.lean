import QuadraticMetricPullbackFirst
import FirstMetricResponseLaws

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

def normalCoordinateCorrection (g : MetricField) : CoordinateQuadraticArray :=
  fun i a b => -leviCivitaCoefficients g 0 i a b

theorem normalCoordinateCorrection_symmetric (g : MetricField) (symmetric : MetricFieldSymmetric g) :
    ∀ i a b, normalCoordinateCorrection g i a b = normalCoordinateCorrection g i b a := by
  intro i a b
  exact congrArg Neg.neg (leviCivita_torsion_free g symmetric 0 i a b)

def normalizingCoordinateMap (g : MetricField) : CoordinatePoint → CoordinatePoint :=
  quadraticIdentityMap (normalCoordinateCorrection g)

theorem normalizingCoordinateMap_local_chart (g : MetricField) :
    SmoothCoordinateAt (normalizingCoordinateMap g) 0 :=
  quadraticCoordinateMap_local_chart _ _ _

theorem normalizingCoordinateMap_zero (g : MetricField) : normalizingCoordinateMap g 0 = 0 :=
  quadraticIdentityMap_zero _

theorem normalizingCoordinateMap_jacobian (g : MetricField) (symmetric : MetricFieldSymmetric g) :
    coordinateJacobian (normalizingCoordinateMap g) 0 = 1 :=
  quadraticIdentityMap_jacobian_zero _ (normalCoordinateCorrection_symmetric g symmetric)

theorem normalizing_metric_partial_zero (g : MetricField) (symmetric : MetricFieldSymmetric g)
    (smooth : ∀ a b, ContDiffAt ℝ ⊤ (fun x => g x a b) 0) (value : g 0 = metric)
    (a b c : Fin 4) :
    scalarPartial (fun x => coordinateMetricPullback g (normalizingCoordinateMap g) x a b) 0 c = 0 := by
  have hn : (g 0).det ≠ 0 := by rw [value, canonical_lorentz_metric_det]; norm_num
  have hc := leviCivita_metric_compatible g symmetric 0 hn a b c
  have h1 : (∑ i : Fin 4, g 0 i b * normalCoordinateCorrection g i a c) =
      -(∑ i : Fin 4, leviCivitaCoefficients g 0 i c a * g 0 i b) := by
    simp only [normalCoordinateCorrection, mul_neg, Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [leviCivita_torsion_free g symmetric 0 i a c]
    ring
  have h2 : (∑ i : Fin 4, g 0 a i * normalCoordinateCorrection g i b c) =
      -(∑ i : Fin 4, leviCivitaCoefficients g 0 i c b * g 0 a i) := by
    simp only [normalCoordinateCorrection, mul_neg, Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [leviCivita_torsion_free g symmetric 0 i b c]
    ring
  unfold normalizingCoordinateMap
  rw [quadratic_identity_metric_pullback_partial g smooth _
    (normalCoordinateCorrection_symmetric g symmetric) a b c, h1, h2, hc]
  ring

theorem normalizing_metric_germ (g : MetricField) (symmetric : MetricFieldSymmetric g)
    (smooth : ∀ a b, ContDiffAt ℝ ⊤ (fun x => g x a b) 0) (value : g 0 = metric) :
    NormalizedSmoothMetricGerm (coordinateMetricPullback g (normalizingCoordinateMap g)) := by
  refine ⟨coordinateMetricPullback_symmetric g symmetric _, ?_, ?_, ?_⟩
  · intro a b
    apply coordinateMetricPullback_contDiffAt g (normalizingCoordinateMap g) 0
      (normalizingCoordinateMap_local_chart g).1
    simpa only [normalizingCoordinateMap_zero] using smooth
  · rw [normalizingCoordinateMap, quadraticIdentityMap,
      quadratic_metric_pullback_value _ _ _ _ (normalCoordinateCorrection_symmetric g symmetric),
      coordinateFrameMatrix_refl, Matrix.transpose_one, one_mul, mul_one, value]
  · intro a b
    apply continuousLinearMap_zero_of_coordinate_basis
    intro c
    exact normalizing_metric_partial_zero g symmetric smooth value a b c

theorem natural_response_normalizing_chart (E : MetricFieldResponse) (natural : MetricResponseNatural E)
    (g : MetricField) (symmetric : MetricFieldSymmetric g) :
    E (coordinateMetricPullback g (normalizingCoordinateMap g)) 0 = E g 0 := by
  have h := natural (normalizingCoordinateMap g) 0 (normalizingCoordinateMap_local_chart g) g
  simpa only [normalizingCoordinateMap_jacobian g symmetric, normalizingCoordinateMap_zero,
    Matrix.transpose_one, one_mul, mul_one] using h

#print axioms normalCoordinateCorrection_symmetric
#print axioms normalizingCoordinateMap_local_chart
#print axioms normalizingCoordinateMap_zero
#print axioms normalizingCoordinateMap_jacobian
#print axioms normalizing_metric_partial_zero
#print axioms normalizing_metric_germ
#print axioms natural_response_normalizing_chart
end
end AASCSemanticExhaustion
