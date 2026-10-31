import CompletedConeClock
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Module.LinearMap.End

/-!
A finite actual-rest-comparison branch of SR Proposition 5.6. The manuscript
allows an arbitrary rest group; this file proves a sufficient finite-group
branch by an explicit orbit sum. It does not assume a compact orbit, a spatial
inner product, a positive clock, or a finite propagation bound.
-/

namespace AASCMetricConstruction

open scoped BigOperators

variable {V H : Type*} [AddCommGroup V] [Module ℝ V]
variable [Group H] [Fintype H]

omit [Module ℝ V] [Group H] [Fintype H] in
private theorem sum_mem_additive_set
    (C : Set V) (zero_mem : (0 : V) ∈ C)
    (add_mem : ∀ u ∈ C, ∀ v ∈ C, u + v ∈ C)
    (s : Finset H) (f : H → V) (hf : ∀ h ∈ s, f h ∈ C) :
    ∑ h ∈ s, f h ∈ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem
  | @insert h s hnot ih =>
    rw [Finset.sum_insert hnot]
    exact add_mem _ (hf h (Finset.mem_insert_self h s)) _
      (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))

/-- Pointed completed order, weak clock monotonicity, an actual finite rest
action, and absence of fixed zero-clock vectors imply strict clock separation.
The only conclusion-bearing condition is fixed-vector exclusion, the explicit
source premise of Proposition 5.6; it does not mention a metric or a bound. -/
theorem positive_clock_of_finite_rest_action
    (C : Set V) (zero_mem : (0 : V) ∈ C)
    (add_mem : ∀ u ∈ C, ∀ v ∈ C, u + v ∈ C)
    (pointed : ∀ v ∈ C, -v ∈ C → v = 0)
    (τ : V →ₗ[ℝ] ℝ)
    (nonnegative : ∀ v ∈ C, 0 ≤ τ v)
    (ρ : H →* Module.End ℝ V)
    (preserves_cone : ∀ h v, v ∈ C → ρ h v ∈ C)
    (preserves_clock : ∀ h v, τ (ρ h v) = τ v)
    (no_fixed_spatial : ∀ v, τ v = 0 → (∀ h, ρ h v = v) → v = 0) :
    ∀ v ∈ C, v ≠ 0 → 0 < τ v := by
  classical
  intro v hv hvzero
  have hτ := nonnegative v hv
  by_contra hnot
  have hτzero : τ v = 0 := le_antisymm (le_of_not_gt hnot) hτ
  let orbitSum : V := ∑ h : H, ρ h v
  have sum_clock : τ orbitSum = 0 := by
    simp [orbitSum, map_sum, preserves_clock, hτzero]
  have sum_fixed : ∀ k, ρ k orbitSum = orbitSum := by
    intro k
    change ρ k (∑ h : H, ρ h v) = ∑ h : H, ρ h v
    rw [map_sum]
    have act_mul : ∀ h, ρ k (ρ h v) = ρ (k * h) v := by
      intro h
      rw [map_mul]
      rfl
    simp_rw [act_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft k)
      (fun h : H => ρ (k * h) v) (fun h : H => ρ h v) (fun _ => rfl)
  have sum_zero : orbitSum = 0 := no_fixed_spatial orbitSum sum_clock sum_fixed
  let restSum : V := ∑ h ∈ (Finset.univ.erase (1 : H)), ρ h v
  have rest_mem : restSum ∈ C := by
    apply sum_mem_additive_set C zero_mem add_mem
    intro h _
    exact preserves_cone h v hv
  have rest_add : restSum + v = 0 := by
    have hs := Finset.sum_erase_add (Finset.univ : Finset H)
      (fun h : H => ρ h v) (Finset.mem_univ (1 : H))
    have h1 : ρ (1 : H) v = v := by rw [map_one]; rfl
    change restSum + ρ (1 : H) v = orbitSum at hs
    rw [h1, sum_zero] at hs
    exact hs
  have rest_eq : restSum = -v := eq_neg_of_add_eq_zero_left rest_add
  apply hvzero
  exact pointed v hv (rest_eq ▸ rest_mem)

/-- Composition with the fully proved general finite-dimensional cone lemma.
This returns an inhabited compact clock section and a finite comparison bound;
it does not return a Lorentzian metric. -/
theorem finite_rest_action_constructs_clock_section
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (C : Set V) (closed : IsClosed C)
    (zero_mem : (0 : V) ∈ C)
    (add_mem : ∀ u ∈ C, ∀ v ∈ C, u + v ∈ C)
    (conic : ∀ r : ℝ, 0 ≤ r → ∀ v ∈ C, r • v ∈ C)
    (pointed : ∀ v ∈ C, -v ∈ C → v = 0)
    (τ : V →L[ℝ] ℝ)
    (nonnegative : ∀ v ∈ C, 0 ≤ τ v)
    (ρ : H →* Module.End ℝ V)
    (preserves_cone : ∀ h v, v ∈ C → ρ h v ∈ C)
    (preserves_clock : ∀ h v, τ (ρ h v) = τ v)
    (no_fixed_spatial : ∀ v, τ v = 0 → (∀ h, ρ h v = v) → v = 0)
    (occupied : ∃ v ∈ C, v ≠ 0) :
    (ClockSection C τ).Nonempty ∧ IsCompact (ClockSection C τ) ∧
      ∃ M : ℝ, 0 < M ∧ ∀ v ∈ C, ‖v‖ ≤ M * τ v := by
  have positive := positive_clock_of_finite_rest_action C zero_mem add_mem
    pointed τ.toLinearMap nonnegative ρ preserves_cone preserves_clock no_fixed_spatial
  exact ⟨clock_section_nonempty C conic τ positive occupied,
    clock_section_compact C closed conic τ positive,
    finite_comparison_bound C closed conic τ positive⟩

#print axioms positive_clock_of_finite_rest_action
#print axioms finite_rest_action_constructs_clock_section

end AASCMetricConstruction
