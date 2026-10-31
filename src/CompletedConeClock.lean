import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
Source: Special Relativity from AASC, reference edition, Lemma 5.5 (PDF p.26).
The ambient norm is auxiliary. It is not asserted to be a physical spatial
metric. The completed cone, original clock and their physical interpretation
are branch inputs; a finite comparison bound and compact clock slice are derived.
-/

namespace AASCMetricConstruction

open Set NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def ClockSection (C : Set V) (τ : V →L[ℝ] ℝ) : Set V :=
  {v | v ∈ C ∧ τ v = 1}

/-- Strict clock separation on a closed completed cone yields a finite bound
in any chosen auxiliary norm. No bound, compact clock section, or spatial
quadratic form is supplied as a premise. -/
theorem finite_comparison_bound [FiniteDimensional ℝ V]
    (C : Set V) (closed : IsClosed C)
    (conic : ∀ r : ℝ, 0 ≤ r → ∀ v ∈ C, r • v ∈ C)
    (τ : V →L[ℝ] ℝ)
    (positive : ∀ v ∈ C, v ≠ 0 → 0 < τ v) :
    ∃ M : ℝ, 0 < M ∧ ∀ v ∈ C, ‖v‖ ≤ M * τ v := by
  let S : Set V := Metric.sphere (0 : V) 1 ∩ C
  have compact : IsCompact S := (isCompact_sphere (0 : V) 1).inter_right closed
  have pos_on : ∀ v ∈ S, 0 < τ v := by
    intro v hv
    have norm_one : ‖v‖ = 1 := by simpa using hv.1
    apply positive v hv.2
    intro hzero
    simp [hzero] at norm_one
  obtain ⟨ε, hε, lower⟩ := compact.exists_forall_le' τ.continuous.continuousOn pos_on
  refine ⟨ε⁻¹, inv_pos.mpr hε, ?_⟩
  intro v hv
  by_cases hzero : v = 0
  · subst v; simp
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hzero
  have hnormalized : normalize v ∈ S := by
    constructor
    · simpa using norm_normalize hzero
    · exact conic ‖v‖⁻¹ (inv_nonneg.mpr (norm_nonneg v)) v hv
  have hlower := lower (normalize v) hnormalized
  have hvalue : τ (normalize v) = ‖v‖⁻¹ * τ v := by
    simp [NormedSpace.normalize]
  rw [hvalue] at hlower
  have hscaled := mul_le_mul_of_nonneg_left hlower (le_of_lt hnorm)
  have hεnorm : ε * ‖v‖ ≤ τ v := by
    simpa [mul_assoc, ne_of_gt hnorm, mul_comm] using hscaled
  have hresult := mul_le_mul_of_nonneg_left hεnorm (le_of_lt (inv_pos.mpr hε))
  simpa [mul_assoc, ne_of_gt hε] using hresult

/-- A nonzero original cone record produces an actual point of the clock-one
section by rescaling. This nonemptiness is constructed, not a subtype field. -/
theorem clock_section_nonempty
    (C : Set V)
    (conic : ∀ r : ℝ, 0 ≤ r → ∀ v ∈ C, r • v ∈ C)
    (τ : V →L[ℝ] ℝ)
    (positive : ∀ v ∈ C, v ≠ 0 → 0 < τ v)
    (occupied : ∃ v ∈ C, v ≠ 0) :
    (ClockSection C τ).Nonempty := by
  obtain ⟨v, hv, hvzero⟩ := occupied
  have hτ := positive v hv hvzero
  refine ⟨(τ v)⁻¹ • v, conic _ (inv_nonneg.mpr hτ.le) v hv, ?_⟩
  simp [ne_of_gt hτ]

theorem clock_section_compact [FiniteDimensional ℝ V]
    (C : Set V) (closed : IsClosed C)
    (conic : ∀ r : ℝ, 0 ≤ r → ∀ v ∈ C, r • v ∈ C)
    (τ : V →L[ℝ] ℝ)
    (positive : ∀ v ∈ C, v ≠ 0 → 0 < τ v) :
    IsCompact (ClockSection C τ) := by
  obtain ⟨M, _, bound⟩ := finite_comparison_bound C closed conic τ positive
  have hclosed : IsClosed (ClockSection C τ) :=
    closed.inter (isClosed_eq τ.continuous continuous_const)
  have hsubset : ClockSection C τ ⊆ Metric.closedBall (0 : V) M := by
    intro v hv
    have h := bound v hv.1
    simpa [hv.2] using h
  exact (isCompact_closedBall (0 : V) M).of_isClosed_subset hclosed hsubset

/-- The converse in Lemma 5.5: weak clock monotonicity and any finite bound
force strict separation of every nonzero completed-cone record. -/
theorem positive_clock_of_finite_bound
    (C : Set V) (τ : V →L[ℝ] ℝ)
    (nonnegative : ∀ v ∈ C, 0 ≤ τ v)
    (M : ℝ) (bound : ∀ v ∈ C, ‖v‖ ≤ M * τ v) :
    ∀ v ∈ C, v ≠ 0 → 0 < τ v := by
  intro v hv hzero
  have hτ := nonnegative v hv
  by_contra hnot
  have heq : τ v = 0 := le_antisymm (le_of_not_gt hnot) hτ
  have h := bound v hv
  rw [heq, mul_zero] at h
  exact hzero (norm_eq_zero.mp (le_antisymm h (norm_nonneg v)))

/-- Both directions retain the exact completed-cone scope. -/
theorem strict_clock_iff_finite_bound [FiniteDimensional ℝ V]
    (C : Set V) (closed : IsClosed C)
    (conic : ∀ r : ℝ, 0 ≤ r → ∀ v ∈ C, r • v ∈ C)
    (τ : V →L[ℝ] ℝ)
    (nonnegative : ∀ v ∈ C, 0 ≤ τ v) :
    (∀ v ∈ C, v ≠ 0 → 0 < τ v) ↔
      ∃ M : ℝ, 0 < M ∧ ∀ v ∈ C, ‖v‖ ≤ M * τ v := by
  constructor
  · exact finite_comparison_bound C closed conic τ
  · rintro ⟨M, _, hM⟩
    exact positive_clock_of_finite_bound C τ nonnegative M hM

#print axioms finite_comparison_bound
#print axioms clock_section_nonempty
#print axioms clock_section_compact
#print axioms positive_clock_of_finite_bound
#print axioms strict_clock_iff_finite_bound

end AASCMetricConstruction
