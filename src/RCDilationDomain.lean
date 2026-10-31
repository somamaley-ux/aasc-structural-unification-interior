import RCConformalScaleBounds

/-! Actual dilation map, derivative and compact receiving-domain coverage.
The normalized sampled metric and the true pullback are distinct. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG AASCKleinGordon.SameActionSource
open scoped Topology BigOperators
namespace AASCKleinGordon.RecoveryComparison

def dilationCLM (epsilon : ℝ) : CoordinatePoint →L[ℝ] CoordinatePoint :=
  epsilon • ContinuousLinearMap.id ℝ CoordinatePoint

def normalizedRescaledMetric (a : Parameters) (epsilon : ℝ) : MetricField :=
  fun y => sourceMetric a (epsilon • y)

def actualDilationPullback (a : Parameters) (epsilon : ℝ) : MetricField := fun y i j =>
  coordinateMetricPairing (sourceMetric a (epsilon • y))
    (dilationCLM epsilon (Pi.single i 1)) (dilationCLM epsilon (Pi.single j 1))

theorem actual_dilation_derivative (epsilon : ℝ) (y : CoordinatePoint) :
    HasFDerivAt (fun p : CoordinatePoint => epsilon • p) (dilationCLM epsilon) y := by
  exact (hasFDerivAt_id y).const_smul epsilon

theorem actual_dilation_pullback_formula (a : Parameters) (epsilon : ℝ) (y : CoordinatePoint) :
    actualDilationPullback a epsilon y = epsilon^2 • normalizedRescaledMetric a epsilon y := by
  ext i j
  simp [actualDilationPullback,coordinateMetricPairing,dilationCLM,normalizedRescaledMetric,
    Pi.single_apply,pow_two,mul_comm,mul_left_comm,mul_assoc]

theorem diamond_gauge_dilation (epsilon : ℝ) (y : CoordinatePoint) :
    diamondGauge (epsilon • y) = |epsilon| * diamondGauge y := by
  simp only [diamondGauge,Pi.smul_apply,smul_eq_mul,abs_mul,map_smul,Prod.smul_snd,norm_smul,
    Real.norm_eq_abs]
  ring

theorem compact_dilation_receiving_domain (a : Parameters) (K : Set CoordinatePoint) (compact : IsCompact K) :
    ∃ epsilon0 B : ℝ, 0 < epsilon0 ∧ 0 < B ∧
      (∀ y ∈ K, diamondGauge y ≤ B) ∧
      ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ epsilon0 → ∀ y ∈ K,
        epsilon • y ∈ sourceDomain a ∧ |conformalFrequency a*(epsilon • y) 0| ≤ (1:ℝ)/2 := by
  obtain ⟨C,bound⟩ := compact.exists_bound_of_continuousOn (f := diamondGauge) diamond_gauge_continuous.continuousOn
  let B := |C|+1
  have Bpos : 0 < B := by dsimp [B];positivity
  have pointBound : ∀ y ∈ K, diamondGauge y ≤ B := by
    intro y hy
    have b := bound y hy
    rw [Real.norm_eq_abs] at b
    exact (le_abs_self _).trans (b.trans ((le_abs_self C).trans (by dsimp [B];linarith)))
  let epsilon0 := min (protectedRadius (conformalFrequency a)/(2*B))
    (1/(2*(|conformalFrequency a|+1)*B))
  have epos : 0 < epsilon0 := by
    dsimp [epsilon0]
    exact lt_min (div_pos (protected_radius_positive _) (by positivity)) (by positivity)
  refine ⟨epsilon0,B,epos,Bpos,pointBound,?_⟩
  intro epsilon he he0 y hy
  have first : epsilon ≤ protectedRadius (conformalFrequency a)/(2*B) := he0.trans (min_le_left _ _)
  have second : epsilon ≤ 1/(2*(|conformalFrequency a|+1)*B) := he0.trans (min_le_right _ _)
  have firstProduct := (le_div_iff₀ (show 0 < 2*B by positivity)).mp first
  have secondProduct := (le_div_iff₀ (show 0 < 2*(|conformalFrequency a|+1)*B by positivity)).mp second
  have timeBound : |y 0| ≤ B :=
    (le_add_of_nonneg_right (norm_nonneg ((coordinateSpatialSplit y).2))).trans (pointBound y hy)
  have epsPoint : epsilon*diamondGauge y ≤ epsilon*B := mul_le_mul_of_nonneg_left (pointBound y hy) he
  constructor
  · change diamondGauge (epsilon • y) < protectedRadius (conformalFrequency a)
    rw [diamond_gauge_dilation,abs_of_nonneg he]
    nlinarith [protected_radius_positive (conformalFrequency a)]
  · simp only [Pi.smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg he]
    have p := mul_le_mul_of_nonneg_left timeBound (show 0 ≤ |conformalFrequency a| * epsilon by positivity)
    have extra : 0 ≤ epsilon*B := mul_nonneg he Bpos.le
    nlinarith

end AASCKleinGordon.RecoveryComparison
