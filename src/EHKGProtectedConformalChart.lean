import EHKGActualConjugacy

/-! A nonempty protected chart, exact original metric/operator identity and
physical-mass matching. Global hyperbolicity and full Cauchy theory are later
proofs; no such conclusions are smuggled into this chart's hypotheses. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology BigOperators
namespace AASCKleinGordon.CurvedKG

def auxiliaryKGParameters (a : Parameters) : Parameters where
  mass := a.mass / Real.sqrt 2
  speed := a.speed
  hbar := a.hbar
  mass_pos := div_pos a.mass_pos (Real.sqrt_pos.mpr (by norm_num))
  speed_pos := a.speed_pos
  hbar_pos := a.hbar_pos

theorem auxiliary_mass_wave_number (a : Parameters) :
    massWaveNumber (auxiliaryKGParameters a) = conformalFrequency a := by
  dsimp [massWaveNumber, auxiliaryKGParameters, conformalFrequency]
  ring

theorem exists_protected_conformal_chart (nu : ℝ) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ p ∈ Metric.ball (0 : CoordinatePoint) radius,
      originalEHActMetric (conformalOperand nu) p = timeConformalMetric (secantScale nu) p ∧
        0 < Real.cos (nu * p 0) := by
  have nearMetric : ∀ᶠ p : CoordinatePoint in 𝓝 0,
      originalEHActMetric (conformalOperand nu) p = timeConformalMetric (secantScale nu) p :=
    conformal_operand_secant_germ nu
  have positiveSet : {p : CoordinatePoint | 0 < Real.cos (nu * p 0)} ∈ 𝓝 0 := by
    apply (isOpen_lt continuous_const (by fun_prop)).mem_nhds
    simp
  exact Metric.mem_nhds_iff.mp (inter_mem nearMetric positiveSet)

def protectedRadius (nu : ℝ) : ℝ := Classical.choose (exists_protected_conformal_chart nu)

theorem protected_radius_positive (nu : ℝ) : 0 < protectedRadius nu :=
  (Classical.choose_spec (exists_protected_conformal_chart nu)).1

def protectedConformalBall (nu : ℝ) : Set CoordinatePoint := Metric.ball 0 (protectedRadius nu)

theorem protected_ball_open (nu : ℝ) : IsOpen (protectedConformalBall nu) := Metric.isOpen_ball

theorem protected_ball_zero (nu : ℝ) : (0 : CoordinatePoint) ∈ protectedConformalBall nu :=
  Metric.mem_ball_self (protected_radius_positive nu)

theorem protected_metric_identity (nu : ℝ) (p : CoordinatePoint)
    (inside : p ∈ protectedConformalBall nu) :
    originalEHActMetric (conformalOperand nu) p = timeConformalMetric (secantScale nu) p :=
  ((Classical.choose_spec (exists_protected_conformal_chart nu)).2 p inside).1

theorem protected_cosine_positive (nu : ℝ) (p : CoordinatePoint)
    (inside : p ∈ protectedConformalBall nu) : 0 < Real.cos (nu * p 0) :=
  ((Classical.choose_spec (exists_protected_conformal_chart nu)).2 p inside).2

theorem protected_operator_identity (nu : ℝ) (p : CoordinatePoint)
    (inside : p ∈ protectedConformalBall nu) (u : CoordinatePoint → ℝ) :
    scalarFieldWaveOperator (originalEHActMetric (conformalOperand nu)) u p =
      scalarFieldWaveOperator (timeConformalMetric (secantScale nu)) u p := by
  apply scalar_wave_operator_congr_of_eventuallyEq
  filter_upwards [(protected_ball_open nu).mem_nhds inside] with q hq
  exact protected_metric_identity nu q hq

theorem protected_same_eh_conjugacy (a : Parameters) (p : CoordinatePoint)
    (inside : p ∈ protectedConformalBall (conformalFrequency a))
    (u : CoordinatePoint → ℝ) (smooth : ContDiffAt ℝ 2 u p) :
    flatScalarResidual ((massWaveNumber (auxiliaryKGParameters a)) ^ 2)
      (fun x => secantScale (conformalFrequency a) (x 0) * u x) p =
      -(secantScale (conformalFrequency a) (p 0)) ^ 3 *
        (scalarFieldWaveOperator (originalEHActMetric (conformalOperand (conformalFrequency a))) u p -
          (massWaveNumber a) ^ 2 * u p) := by
  rw [auxiliary_mass_wave_number, protected_operator_identity _ _ inside]
  rw [conformal_frequency_mass]
  exact secant_actual_operator_conjugacy _ p
    (ne_of_gt (protected_cosine_positive _ p inside)) u smooth

theorem protected_same_eh_nonflat (a : Parameters) :
    (0 : CoordinatePoint) ∈ protectedConformalBall (conformalFrequency a) ∧
      conformalOperand (conformalFrequency a) ∈ wickOriginalMetricNeighborhood (⊤ : Opens CoordinatePoint) ∧
      loweredConnectionCurvature (originalEHActMetric (conformalOperand (conformalFrequency a)))
        (leviCivitaCoefficients (originalEHActMetric (conformalOperand (conformalFrequency a))))
          0 0 1 0 1 ≠ 0 :=
  ⟨protected_ball_zero _, conformal_admitted_nonflat _ (ne_of_gt (conformal_frequency_positive a))⟩

end AASCKleinGordon.CurvedKG
