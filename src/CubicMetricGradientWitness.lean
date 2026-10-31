import GeometricCoefficientLock

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0
set_option autoImplicit false

abbrev MetricCubicJet := Fin 4 → Fin 4 → CubicArray

def cubicMetricField (C : MetricCubicJet) : MetricField := fun x a b => metric a b + cubicPolynomial (C a b) x

theorem cubicMetricField_c3_normalized (C : MetricCubicJet)
    (symmetric : ∀ a b, C a b = C b a) : C3NormalizedMetricGerm (cubicMetricField C) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x a b
    have hm : metric a b = metric b a := by
      by_cases h : a = b
      · subst b; rfl
      · simp [metric, h, Ne.symm h]
    simp only [cubicMetricField, symmetric a b, hm]
  · intro a b
    exact (contDiff_const.add (cubicPolynomial_smooth (C a b))).contDiffAt.of_le (by simp)
  · ext a b
    simp [cubicMetricField, cubicPolynomial_zero]
  · intro a b
    have hd := ((hasFDerivAt_const (metric a b) (0 : CoordinatePoint)).add
      (cubicPolynomial_hasFDerivAt (C a b) 0)).fderiv
    change fderiv ℝ (fun x => cubicMetricField C x a b) 0 = _ at hd
    simpa only [zero_add, cubicDerivative_zero] using hd

theorem cubicMetricField_third_partial (C : MetricCubicJet)
    (symmetric : ∀ a b, SymmetricCubicArray (C a b)) (a b c d e : Fin 4) :
    scalarThirdPartial (fun x => cubicMetricField C x a b) 0 c d e = C a b c d e := by
  have hp : (fun x => scalarPartial (fun y => cubicMetricField C y a b) x c) =
      quadraticPolynomial (fun u v => C a b c u v) := by
    funext x
    have hd := ((hasFDerivAt_const (metric a b) x).add (cubicPolynomial_hasFDerivAt (C a b) x)).fderiv
    change fderiv ℝ (fun y => cubicMetricField C y a b) x = _ at hd
    unfold scalarPartial
    rw [hd]
    simp only [zero_add]
    exact symmetric_cubic_derivative_basis (C a b) (symmetric a b) x c
  unfold scalarThirdPartial
  rw [hp]
  change fderiv ℝ (fun x => fderiv ℝ (quadraticPolynomial (fun u v => C a b c u v)) x
    (Pi.single d 1)) 0 (Pi.single e 1) = _
  rw [quadraticPolynomial_second_derivative, (symmetric a b).2 c e d]
  ring

def scalarGradientWitnessJet : MetricCubicJet := fun a b c d e =>
  if a = 1 ∧ b = 1 ∧ c = 0 ∧ d = 0 ∧ e = 0 then 6 else 0

theorem scalarGradientWitnessJet_metric_symmetry (a b : Fin 4) :
    scalarGradientWitnessJet a b = scalarGradientWitnessJet b a := by
  funext c d e
  simp only [scalarGradientWitnessJet]
  congr 1
  apply propext
  tauto

theorem scalarGradientWitnessJet_cubic_symmetry (a b : Fin 4) :
    SymmetricCubicArray (scalarGradientWitnessJet a b) := by
  constructor
  · intro c d e
    simp only [scalarGradientWitnessJet]
    congr 1
    apply propext
    tauto
  · intro c d e
    simp only [scalarGradientWitnessJet]
    congr 1
    apply propext
    tauto

theorem actual_scalar_gradient_witness_time_component :
    coordinateScalarGradient (cubicMetricField scalarGradientWitnessJet) 0 = 6 := by
  have germ := cubicMetricField_c3_normalized scalarGradientWitnessJet scalarGradientWitnessJet_metric_symmetry
  unfold coordinateScalarGradient
  rw [c3_normal_coordinateScalar_partial_diagonal _ germ]
  simp_rw [c3_normal_metric_curvature_partial _ germ,
    cubicMetricField_third_partial scalarGradientWitnessJet scalarGradientWitnessJet_cubic_symmetry]
  norm_num [scalarGradientWitnessJet, metric, Matrix.diagonal_apply, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;>
      (try simp only [Fin.ext_iff]) <;> norm_num

/-- A genuine analytic metric germ with nonzero actual scalar-curvature
gradient. Membership in the original physical comparison family is separate. -/
theorem actual_scalar_gradient_witness_nonzero :
    coordinateScalarGradient (cubicMetricField scalarGradientWitnessJet) ≠ 0 := by
  intro hz
  have h := congrArg (fun v : CoordinatePoint => v 0) hz
  dsimp only at h
  rw [actual_scalar_gradient_witness_time_component] at h
  norm_num at h

theorem cubicMetricField_nondegenerate_neighborhood (C : MetricCubicJet) :
    ∃ U : Set CoordinatePoint, IsOpen U ∧ 0 ∈ U ∧ ∀ x ∈ U, (cubicMetricField C x).det ≠ 0 := by
  have hc : Continuous (cubicMetricField C) := continuous_pi (fun a => continuous_pi
    (fun b => (continuous_const.add (cubicPolynomial_smooth (C a b)).continuous)))
  have hv : cubicMetricField C 0 = metric := by ext a b; simp [cubicMetricField, cubicPolynomial_zero]
  have hn : (cubicMetricField C 0).det ≠ 0 := by rw [hv, canonical_lorentz_metric_det]; norm_num
  obtain ⟨U, hs, ho, hz⟩ := mem_nhds_iff.mp (hc.matrix_det.continuousAt.eventually_ne hn)
  exact ⟨U, ho, hz, fun x hx => hs hx⟩

#print axioms cubicMetricField_c3_normalized
#print axioms cubicMetricField_third_partial
#print axioms scalarGradientWitnessJet_metric_symmetry
#print axioms scalarGradientWitnessJet_cubic_symmetry
#print axioms actual_scalar_gradient_witness_time_component
#print axioms actual_scalar_gradient_witness_nonzero
#print axioms cubicMetricField_nondegenerate_neighborhood
end
end AASCSemanticExhaustion
