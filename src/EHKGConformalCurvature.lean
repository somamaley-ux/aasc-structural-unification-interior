import EHKGCompactConformalOperand
import EHKGCurvatureWitness

/-! Actual nonzero spacetime curvature of the localized conformal EH branch. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology BigOperators
namespace AASCKleinGordon.CurvedKG

theorem conformal_tan_first_zero (nu : ℝ) :
    HasFDerivAt (fun p : CoordinatePoint => Real.tan (nu * p 0))
      (nu • (ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ)) 0 := by
  have first : HasDerivAt Real.tan 1 (nu * (0 : CoordinatePoint) 0) := by
    simpa using (Real.hasDerivAt_tan (by simp : Real.cos (0 : ℝ) ≠ 0))
  simpa using first.comp_hasFDerivAt 0
    ((ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ).hasFDerivAt.const_mul nu)

theorem conformal_tan_regular_zero (nu : ℝ) :
    ContDiffAt ℝ 2 (fun p : CoordinatePoint => Real.tan (nu * p 0)) 0 := by
  have linear : ContDiff ℝ 2 (fun p : CoordinatePoint => nu * p 0) := by fun_prop
  have quotient : ContDiffAt ℝ 2
      (fun p : CoordinatePoint => Real.sin (nu * p 0) / Real.cos (nu * p 0)) 0 :=
    linear.contDiffAt.sin.div linear.contDiffAt.cos (by simp)
  simpa only [Real.tan_eq_sin_div_cos] using quotient

theorem conformal_tan_partial_zero (nu : ℝ) (c : Fin 4) :
    scalarPartial (fun p : CoordinatePoint => Real.tan (nu * p 0)) 0 c =
      nu * (if c = 0 then 1 else 0) := by
  simp [scalarPartial, (conformal_tan_first_zero nu).fderiv, Pi.single_apply, eq_comm]

theorem conformal_seed_first_zero (nu : ℝ) :
    fderiv ℝ (conformalSeed nu) 0 = 0 := by
  simpa [conformalSeed] using ((conformal_tan_first_zero nu).pow 2).fderiv

theorem conformal_seed_second_zero (nu : ℝ) (c d : Fin 4) :
    scalarSecondPartial (conformalSeed nu) 0 c d =
      2 * nu ^ 2 * (if c = 0 then 1 else 0) * (if d = 0 then 1 else 0) := by
  have square : conformalSeed nu =
      (fun p : CoordinatePoint => Real.tan (nu * p 0) * Real.tan (nu * p 0)) := by
    funext p
    simp [conformalSeed, pow_two]
  rw [square, c2_local_scalarSecondPartial_mul _ _ 0
    (conformal_tan_regular_zero nu) (conformal_tan_regular_zero nu)]
  simp only [Pi.zero_apply, mul_zero, Real.tan_zero, zero_mul, zero_add,
    conformal_tan_partial_zero]
  ring

def conformalSeedMetric (nu : ℝ) : MetricField :=
  fun p i j => metric i j + metric i j * conformalSeed nu p

theorem conformal_seed_metric_germ (nu : ℝ) : C2NormalizedMetricGerm (conformalSeedMetric nu) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p i j
    fin_cases i <;> fin_cases j <;> simp [conformalSeedMetric, metric]
  · intro i j
    exact contDiffAt_const.add (contDiffAt_const.mul ((conformal_tan_regular_zero nu).pow 2))
  · funext i j
    simp [conformalSeedMetric, conformalSeed]
  · intro i j
    simp only [conformalSeedMetric, fderiv_const_add]
    have regular : ContDiffAt ℝ 2 (conformalSeed nu) 0 := (conformal_tan_regular_zero nu).pow 2
    rw [fderiv_const_mul (regular.differentiableAt (by norm_num)) (metric i j), conformal_seed_first_zero]
    simp

theorem conformal_actual_near_seed_metric (nu : ℝ) :
    originalEHActMetric (conformalOperand nu) =ᶠ[𝓝 0] conformalSeedMetric nu := by
  filter_upwards [conformal_profile_germ nu] with p hp
  rw [conformal_operand_actual_metric]
  funext i j
  change (1 + conformalProfile nu p) * metric i j = metric i j + metric i j * conformalSeed nu p
  rw [hp]
  ring

theorem conformal_actual_normalized_germ (nu : ℝ) :
    C2NormalizedMetricGerm (originalEHActMetric (conformalOperand nu)) := by
  have near := conformal_actual_near_seed_metric nu
  have germ := conformal_seed_metric_germ nu
  refine ⟨original_eh_act_metric_symmetric _, ?_, ?_, ?_⟩
  · intro i j
    exact (original_eh_act_metric_smooth _ i j).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  · exact (Filter.EventuallyEq.eq_of_nhds near).trans germ.2.2.1
  · intro i j
    have entries : (fun p => originalEHActMetric (conformalOperand nu) p i j) =ᶠ[𝓝 0]
        (fun p => conformalSeedMetric nu p i j) :=
      near.mono (fun p hp => congrArg (fun M : Tensor2 => M i j) hp)
    exact (Filter.EventuallyEq.fderiv_eq entries).trans (germ.2.2.2 i j)

theorem conformal_seed_metric_second (nu : ℝ) (i j c d : Fin 4) :
    scalarSecondPartial (fun p => conformalSeedMetric nu p i j) 0 c d =
      metric i j * (2 * nu ^ 2 * (if c = 0 then 1 else 0) * (if d = 0 then 1 else 0)) := by
  unfold conformalSeedMetric
  have regular : ContDiffAt ℝ 2 (conformalSeed nu) 0 := (conformal_tan_regular_zero nu).pow 2
  rw [scalar_second_constant_add, c2_local_scalarSecondPartial_const_mul (metric i j)
    (conformalSeed nu) 0 regular c d, conformal_seed_second_zero]

theorem conformal_actual_curvature (nu : ℝ) :
    loweredConnectionCurvature (originalEHActMetric (conformalOperand nu))
      (leviCivitaCoefficients (originalEHActMetric (conformalOperand nu))) 0 0 1 0 1 = -nu ^ 2 := by
  rw [c2_normalized_leviCivita_twojet_congr _ _ (conformal_actual_normalized_germ nu)
    (conformal_seed_metric_germ nu)
    (metric_twojet_of_eventuallyEq _ _ 0 (conformal_actual_near_seed_metric nu))]
  rw [c2_normalized_metric_leviCivita_curvature _ (conformal_seed_metric_germ nu)]
  change (1 / 2 : ℝ) *
    (scalarSecondPartial (fun p => conformalSeedMetric nu p 0 1) 0 1 0 +
      scalarSecondPartial (fun p => conformalSeedMetric nu p 1 0) 0 0 1 -
      scalarSecondPartial (fun p => conformalSeedMetric nu p 0 0) 0 1 1 -
      scalarSecondPartial (fun p => conformalSeedMetric nu p 1 1) 0 0 0) = -nu ^ 2
  simp [conformal_seed_metric_second, metric, Matrix.diagonal_apply]

theorem conformal_admitted_nonflat (nu : ℝ) (nonzero : nu ≠ 0) :
    conformalOperand nu ∈ wickOriginalMetricNeighborhood (⊤ : Opens CoordinatePoint) ∧
      loweredConnectionCurvature (originalEHActMetric (conformalOperand nu))
        (leviCivitaCoefficients (originalEHActMetric (conformalOperand nu))) 0 0 1 0 1 ≠ 0 := by
  refine ⟨conformal_operand_admitted nu, ?_⟩
  rw [conformal_actual_curvature]
  exact neg_ne_zero.mpr (pow_ne_zero 2 nonzero)

end AASCKleinGordon.CurvedKG
