import EHKGCurvedOperand
import C2MetricLeviCivita
import C2LocalSecondJetCalculus
import LocalMetricJetCongruence

/-! Nonzero actual spacetime curvature of the compact original EH operand.
The polynomial germ is used through proved local metric/jet equalities; no
curvature or evolution certificate is an input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

theorem time_coordinate_first (p : CoordinatePoint) (c : Fin 4) :
    scalarPartial (fun x : CoordinatePoint => x 0) p c = if c = 0 then 1 else 0 := by
  change fderiv ℝ (ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ) p
    (Pi.single c 1) = _
  rw [ContinuousLinearMap.fderiv]
  simp [Pi.single_apply, eq_comm]

theorem time_square_first_zero (epsilon : ℝ) :
    fderiv ℝ (fun p : CoordinatePoint => epsilon * (p 0) ^ 2) 0 = 0 := by
  have first : HasFDerivAt (fun p : CoordinatePoint => p 0)
      (ContinuousLinearMap.proj (0 : Fin 4)) 0 :=
    (ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ).hasFDerivAt
  simpa using ((first.pow 2).const_mul epsilon).fderiv

theorem scalar_second_constant_add (r : ℝ) (f : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (c d : Fin 4) :
    scalarSecondPartial (fun x => r + f x) p c d = scalarSecondPartial f p c d := by
  simp only [scalarSecondPartial, scalarPartial, fderiv_const_add]

theorem time_square_second (epsilon : ℝ) (c d : Fin 4) :
    scalarSecondPartial (fun p : CoordinatePoint => epsilon * (p 0) ^ 2) 0 c d =
      2 * epsilon * (if c = 0 then 1 else 0) * (if d = 0 then 1 else 0) := by
  have smooth : ContDiffAt ℝ 2 (fun p : CoordinatePoint => p 0) 0 :=
    (ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ).contDiff.contDiffAt
  rw [c2_local_scalarSecondPartial_const_mul epsilon _ 0 (smooth.pow 2)]
  have square : (fun p : CoordinatePoint => (p 0) ^ 2) = (fun p => p 0 * p 0) := by
    funext p
    ring
  rw [square, c2_local_scalarSecondPartial_mul _ _ 0 smooth smooth]
  simp only [Pi.zero_apply, zero_mul, zero_add, time_coordinate_first]
  ring

theorem curvature_polynomial_metric_symmetric (epsilon : ℝ) :
    MetricFieldSymmetric (curvaturePolynomialMetric epsilon) := by
  intro p i j
  fin_cases i <;> fin_cases j <;> simp [curvaturePolynomialMetric, metric]

theorem curvature_polynomial_metric_regular (epsilon : ℝ) (i j : Fin 4) :
    ContDiffAt ℝ 2 (fun p => curvaturePolynomialMetric epsilon p i j) 0 := by
  unfold curvaturePolynomialMetric
  split_ifs <;> fun_prop

theorem curvature_polynomial_metric_zero (epsilon : ℝ) :
    curvaturePolynomialMetric epsilon 0 = metric := by
  funext i j
  simp [curvaturePolynomialMetric]

theorem curvature_polynomial_first_zero (epsilon : ℝ) (i j : Fin 4) :
    fderiv ℝ (fun p => curvaturePolynomialMetric epsilon p i j) 0 = 0 := by
  unfold curvaturePolynomialMetric
  split_ifs
  · rw [fderiv_const_add]
    exact time_square_first_zero epsilon
  · simp

theorem curvature_polynomial_germ (epsilon : ℝ) :
    C2NormalizedMetricGerm (curvaturePolynomialMetric epsilon) :=
  ⟨curvature_polynomial_metric_symmetric epsilon,
    curvature_polynomial_metric_regular epsilon,
    curvature_polynomial_metric_zero epsilon,
    curvature_polynomial_first_zero epsilon⟩

theorem curvature_polynomial_second (epsilon : ℝ) (i j c d : Fin 4) :
    scalarSecondPartial (fun p => curvaturePolynomialMetric epsilon p i j) 0 c d =
      if i = 1 ∧ j = 1 then
        2 * epsilon * (if c = 0 then 1 else 0) * (if d = 0 then 1 else 0) else 0 := by
  by_cases special : i = 1 ∧ j = 1
  · simp only [curvaturePolynomialMetric, special, and_self, if_true]
    rw [scalar_second_constant_add, time_square_second]
  · simp only [curvaturePolynomialMetric, special, if_false, add_zero]
    simp [scalarSecondPartial, scalarPartial]

theorem curved_operand_normalized_germ (epsilon : ℝ) :
    C2NormalizedMetricGerm (originalEHActMetric (curvedOperand epsilon)) := by
  have near := curved_operand_metric_near_polynomial epsilon
  refine ⟨original_eh_act_metric_symmetric _, ?_, ?_, ?_⟩
  · intro i j
    exact (original_eh_act_metric_smooth _ i j).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  · exact (Filter.EventuallyEq.eq_of_nhds near).trans (curvature_polynomial_metric_zero epsilon)
  · intro i j
    have entries : (fun p => originalEHActMetric (curvedOperand epsilon) p i j) =ᶠ[𝓝 0]
        (fun p => curvaturePolynomialMetric epsilon p i j) :=
      near.mono (fun p hp => congrArg (fun M : Tensor2 => M i j) hp)
    exact (Filter.EventuallyEq.fderiv_eq entries).trans (curvature_polynomial_first_zero epsilon i j)

theorem curvature_polynomial_actual_curvature (epsilon : ℝ) :
    loweredConnectionCurvature (curvaturePolynomialMetric epsilon)
      (leviCivitaCoefficients (curvaturePolynomialMetric epsilon)) 0 0 1 0 1 = -epsilon := by
  rw [c2_normalized_metric_leviCivita_curvature _ (curvature_polynomial_germ epsilon)]
  change (1 / 2 : ℝ) *
    (scalarSecondPartial (fun p => curvaturePolynomialMetric epsilon p 0 1) 0 1 0 +
      scalarSecondPartial (fun p => curvaturePolynomialMetric epsilon p 1 0) 0 0 1 -
      scalarSecondPartial (fun p => curvaturePolynomialMetric epsilon p 0 0) 0 1 1 -
      scalarSecondPartial (fun p => curvaturePolynomialMetric epsilon p 1 1) 0 0 0) = -epsilon
  simp [curvature_polynomial_second]

theorem curved_operand_actual_curvature (epsilon : ℝ) :
    loweredConnectionCurvature (originalEHActMetric (curvedOperand epsilon))
      (leviCivitaCoefficients (originalEHActMetric (curvedOperand epsilon))) 0 0 1 0 1 = -epsilon := by
  rw [c2_normalized_leviCivita_twojet_congr _ _ (curved_operand_normalized_germ epsilon)
    (curvature_polynomial_germ epsilon)
    (metric_twojet_of_eventuallyEq _ _ 0 (curved_operand_metric_near_polynomial epsilon))]
  exact curvature_polynomial_actual_curvature epsilon

theorem exists_admitted_curved_original_eh_operand :
    ∃ H : MetricSourceProbe (⊤ : Opens CoordinatePoint),
      H ∈ wickOriginalMetricNeighborhood (⊤ : Opens CoordinatePoint) ∧
        loweredConnectionCurvature (originalEHActMetric H)
          (leviCivitaCoefficients (originalEHActMetric H)) 0 0 1 0 1 ≠ 0 := by
  obtain ⟨epsilon, positive, inside⟩ := exists_positive_curved_operand_admitted
  refine ⟨curvedOperand epsilon, inside, ?_⟩
  rw [curved_operand_actual_curvature]
  exact neg_ne_zero.mpr (ne_of_gt positive)

end AASCKleinGordon.CurvedKG
