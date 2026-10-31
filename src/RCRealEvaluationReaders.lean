import RCInitialSourceComparison

/-! Restricted actual value/coordinate-time evaluation readers on the common
domain. Their shared domain guards are exact; successful numeric answers are
compared quantitatively. These are not all curved/flat physical source uses. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG AASCKleinGordon.SameActionSource
open scoped Topology
namespace AASCKleinGordon.RecoveryComparison
attribute [local instance] Classical.propDecidable

inductive EvaluationKind where
  | value
  | coordinateTimeJet

abbrev EvaluationQuestion := EvaluationKind × CoordinatePoint

def comparisonField (a : Parameters) (f h : CurvedCauchyDatum a) (curved : Bool) : CoordinatePoint → ℝ :=
  if curved then sourceField a f h else flatComparisonField a f h

def evaluationRead (a : Parameters) (f h : CurvedCauchyDatum a) (curved : Bool)
    (q : EvaluationQuestion) : Option ℝ :=
  if q.2 ∈ sourceDomain a then
    some (match q.1 with
      | .value => comparisonField a f h curved q.2
      | .coordinateTimeJet => scalarPartial (comparisonField a f h curved) q.2 0)
  else none

theorem evaluation_domain_exact (a : Parameters) (f h : CurvedCauchyDatum a)
    (curved : Bool) (q : EvaluationQuestion) : (evaluationRead a f h curved q).isSome = true ↔ q.2 ∈ sourceDomain a := by
  unfold evaluationRead
  split_ifs <;> simp_all

theorem evaluation_same_domain_guards (a : Parameters) (f h : CurvedCauchyDatum a) (q : EvaluationQuestion) :
    (evaluationRead a f h true q).isSome = (evaluationRead a f h false q).isSome := by
  by_cases inside : q.2 ∈ sourceDomain a <;> simp [evaluationRead,inside]

def evaluationFirstFailure (a : Parameters) (f h : CurvedCauchyDatum a) (curved : Bool)
    (questions : List EvaluationQuestion) : Option ℕ :=
  questions.findIdx? (fun q => !(evaluationRead a f h curved q).isSome)

theorem evaluation_first_domain_failure_exact (a : Parameters) (f h : CurvedCauchyDatum a)
    (questions : List EvaluationQuestion) :
    evaluationFirstFailure a f h true questions = evaluationFirstFailure a f h false questions := by
  unfold evaluationFirstFailure
  congr 1
  funext q
  rw [evaluation_same_domain_guards]

theorem curved_value_reader_is_original (a : Parameters) (f h : CurvedCauchyDatum a) (p : CoordinatePoint) :
    evaluationRead a f h true (.value,p) =
      scalarQuestionAnswer a (initialCurvedScalarUseState a f h) (.value p) := by
  rfl

theorem actual_evaluation_comparison (a : Parameters) (f h : CurvedCauchyDatum a)
    (K : Set KGSpatialSpace) (compact : IsCompact K)
    (interior : K ⊆ centralLeafDomain (conformalFrequency a)) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ r → ∀ x ∈ K,
      (∃ u v : ℝ, evaluationRead a f h true (.value,spaceTimePoint t x)=some u ∧
        evaluationRead a f h false (.value,spaceTimePoint t x)=some v ∧ |u-v| ≤ C*t^2) ∧
      (∃ u v : ℝ, evaluationRead a f h true (.coordinateTimeJet,spaceTimePoint t x)=some u ∧
        evaluationRead a f h false (.coordinateTimeJet,spaceTimePoint t x)=some v ∧ |u-v| ≤ C*|t|) := by
  obtain ⟨r,C,hr,hC,domain,bounds⟩ := same_data_local_evolved_comparison a f h K compact interior
  refine ⟨r,C,hr,hC,?_⟩
  intro t ht x hx
  have inside := domain t ht x hx
  constructor
  · refine ⟨sourceField a f h (spaceTimePoint t x),flatComparisonField a f h (spaceTimePoint t x),?_,?_,(bounds t ht x hx).1⟩ <;>
      simp [evaluationRead,comparisonField,inside]
  · refine ⟨scalarPartial (sourceField a f h) (spaceTimePoint t x) 0,
      scalarPartial (flatComparisonField a f h) (spaceTimePoint t x) 0,?_,?_,(bounds t ht x hx).2⟩ <;>
      simp [evaluationRead,comparisonField,inside]

theorem same_data_physical_time_comparison (a : Parameters) (f h : CurvedCauchyDatum a)
    (K : Set KGSpatialSpace) (compact : IsCompact K)
    (interior : K ⊆ centralLeafDomain (conformalFrequency a)) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ r → ∀ x ∈ K,
      spaceTimePoint (a.speed*t) x ∈ sourceDomain a ∧
      |sourceField a f h (spaceTimePoint (a.speed*t) x)-flatComparisonField a f h (spaceTimePoint (a.speed*t) x)| ≤ C*t^2 ∧
      |deriv (fun s => sourceField a f h (spaceTimePoint (a.speed*s) x)) t-
        deriv (fun s => flatComparisonField a f h (spaceTimePoint (a.speed*s) x)) t| ≤ C*|t| := by
  obtain ⟨r,C,hr,hC,domain,bound⟩ := same_data_local_evolved_comparison a f h K compact interior
  refine ⟨r/a.speed,C*a.speed^2,div_pos hr a.speed_pos,mul_nonneg hC (sq_nonneg _),?_⟩
  intro t ht x hx
  have inside : |a.speed*t| ≤ r := by
    rw [abs_mul,abs_of_pos a.speed_pos]
    have h := (le_div_iff₀ a.speed_pos).mp ht
    nlinarith
  have estimates := bound (a.speed*t) inside x hx
  refine ⟨domain _ inside x hx,?_,?_⟩
  · convert estimates.1 using 1 <;> ring
  · rw [(scalar_physical_time_derivative a _ (source_field_smooth a f h) t x).deriv,
      (scalar_physical_time_derivative a _ (fixed_mass_flat_field_smooth a _ f h) t x).deriv,
      ←mul_sub,abs_mul,abs_of_pos a.speed_pos]
    have scaled := mul_le_mul_of_nonneg_left estimates.2 a.speed_pos.le
    rw [abs_mul,abs_of_pos a.speed_pos] at scaled
    convert scaled using 1 <;> ring

end AASCKleinGordon.RecoveryComparison
