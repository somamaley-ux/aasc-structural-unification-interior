import FiniteRestClockSeparation

/-!
The finite-rest-action source branch of SR Definition 5.4, Proposition 5.6,
and Lemma 5.5. Reach is constructed from the original increment set by finite
addition and nonnegative rescaling, followed by declared topological completion.
This is a completed-reach query, not a claim that every limit is an executed path.
-/

namespace AASCMetricConstruction

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

inductive FiniteReach (W : Set V) : V → Prop
  | zero : FiniteReach W 0
  | original {v} : v ∈ W → FiniteReach W v
  | add {u v} : FiniteReach W u → FiniteReach W v → FiniteReach W (u + v)
  | scale (r : ℝ) (hr : 0 ≤ r) {v} : FiniteReach W v → FiniteReach W (r • v)

/-- Exact finite-ledger semantics: the inductive construction is precisely a
finite sum of nonnegative multiples of original increments, including the
empty sum. The construction does not introduce additional finite reach. -/
theorem finiteReach_iff_original_ledger (W : Set V) (v : V) :
    FiniteReach W v ↔
      ∃ ledger : List (ℝ × V),
        (∀ entry ∈ ledger, 0 ≤ entry.1 ∧ entry.2 ∈ W) ∧
        v = (ledger.map (fun entry => entry.1 • entry.2)).sum := by
  constructor
  · intro hv
    induction hv with
    | zero => exact ⟨[], by simp⟩
    | @original v hw =>
      refine ⟨[(1, v)], ?_, ?_⟩
      · intro entry he
        simp only [List.mem_singleton] at he
        subst entry
        exact ⟨by norm_num, hw⟩
      · simp
    | @add u v _ _ ih1 ih2 =>
      obtain ⟨left, hl, hel⟩ := ih1
      obtain ⟨right, hr, her⟩ := ih2
      refine ⟨left ++ right, ?_, ?_⟩
      · intro entry he
        rcases List.mem_append.mp he with h | h
        · exact hl entry h
        · exact hr entry h
      · simpa only [List.map_append, List.sum_append] using congrArg₂ (· + ·) hel her
    | @scale r hr v _ ih =>
      obtain ⟨ledger, hl, he⟩ := ih
      refine ⟨ledger.map (fun entry => (r * entry.1, entry.2)), ?_, ?_⟩
      · intro entry he_mem
        obtain ⟨original, horig, rfl⟩ := List.mem_map.mp he_mem
        exact ⟨mul_nonneg hr (hl original horig).1, (hl original horig).2⟩
      · rw [he]
        simp only [List.map_map, Function.comp_def]
        have distrib : ∀ xs : List (ℝ × V),
            r • (xs.map (fun entry => entry.1 • entry.2)).sum =
              (xs.map (fun entry => (r * entry.1) • entry.2)).sum := by
          intro xs
          induction xs with
          | nil => simp
          | cons head tail ih =>
            simpa only [List.map_cons, List.sum_cons, smul_add, mul_smul] using
              (congrArg (fun z => (r * head.1) • head.2 + z) ih)
        exact distrib ledger
  · rintro ⟨ledger, hvalid, rfl⟩
    induction ledger with
    | nil => simpa using (FiniteReach.zero (W := W))
    | cons head tail ih =>
      have hh := hvalid head List.mem_cons_self
      have ht := ih (fun entry he => hvalid entry (List.mem_cons_of_mem head he))
      simpa using FiniteReach.add (FiniteReach.scale head.1 hh.1 (.original hh.2)) ht

def completedReach (W : Set V) : Set V := closure {v | FiniteReach W v}

theorem original_mem_completedReach (W : Set V) {v : V} (hv : v ∈ W) :
    v ∈ completedReach W :=
  subset_closure (FiniteReach.original hv)

theorem zero_mem_completedReach (W : Set V) : (0 : V) ∈ completedReach W :=
  subset_closure FiniteReach.zero

theorem add_mem_completedReach (W : Set V)
    {u v : V} (hu : u ∈ completedReach W) (hv : v ∈ completedReach W) :
    u + v ∈ completedReach W := by
  have maps : Set.MapsTo (fun z : V => z + v)
      {z | FiniteReach W z} (completedReach W) := by
    intro z hz
    exact map_mem_closure (continuous_const.add continuous_id) hv
      (fun w hw => FiniteReach.add hz hw)
  have h := map_mem_closure (continuous_id.add continuous_const) hu maps
  simpa [completedReach] using h

theorem smul_mem_completedReach (W : Set V) (r : ℝ) (hr : 0 ≤ r)
    {v : V} (hv : v ∈ completedReach W) : r • v ∈ completedReach W := by
  exact map_mem_closure (continuous_const.smul continuous_id) hv
    (fun w hw => FiniteReach.scale r hr hw)

theorem weak_clock_extends_to_completedReach
    (W : Set V) (τ : V →L[ℝ] ℝ)
    (original_nonnegative : ∀ w ∈ W, 0 ≤ τ w) :
    ∀ v ∈ completedReach W, 0 ≤ τ v := by
  have finite_nonnegative : ∀ v, FiniteReach W v → 0 ≤ τ v := by
    intro v hv
    induction hv with
    | zero => simp
    | original hw => exact original_nonnegative _ hw
    | add _ _ ih1 ih2 => simpa using add_nonneg ih1 ih2
    | scale r hr _ ih => simpa using mul_nonneg hr ih
  exact closure_minimal (fun v hv => finite_nonnegative v hv)
    (isClosed_le continuous_const τ.continuous)

theorem increment_map_preserves_completedReach
    (W : Set V) (f : V →L[ℝ] V)
    (preserves_original : ∀ w ∈ W, f w ∈ W) :
    ∀ v ∈ completedReach W, f v ∈ completedReach W := by
  have finite_preservation : ∀ v, FiniteReach W v → FiniteReach W (f v) := by
    intro v hv
    induction hv with
    | zero => simpa using (FiniteReach.zero (W := W))
    | original hw => exact .original (preserves_original _ hw)
    | add _ _ ih1 ih2 => simpa using FiniteReach.add ih1 ih2
    | scale r hr _ ih => simpa using FiniteReach.scale r hr ih
  intro v hv
  exact map_mem_closure f.continuous hv (fun w hw => finite_preservation w hw)

/-- A constructor from original increment records to an occupied compact
clock section. The original records need only have weak nonnegative clock;
strict completed-clock positivity and the finite bound are conclusions.
Pointed completed order and no fixed zero-clock direction remain explicit
physical branch conditions. No metric or quadratic-body premise is used. -/
theorem source_increments_construct_compact_clock_section
    [FiniteDimensional ℝ V]
    {H : Type*} [Group H] [Fintype H]
    (W : Set V) (τ : V →L[ℝ] ℝ)
    (original_nonnegative : ∀ w ∈ W, 0 ≤ τ w)
    (occupied : ∃ w ∈ W, w ≠ 0)
    (completed_order : ∀ v ∈ completedReach W, -v ∈ completedReach W → v = 0)
    (ρ : H →* Module.End ℝ V)
    (original_rest_comparisons : ∀ h w, w ∈ W → ρ h w ∈ W)
    (clock_preservation : ∀ h v, τ (ρ h v) = τ v)
    (no_fixed_spatial : ∀ v, τ v = 0 → (∀ h, ρ h v = v) → v = 0) :
    (∀ v ∈ completedReach W, v ≠ 0 → 0 < τ v) ∧
    (ClockSection (completedReach W) τ).Nonempty ∧
    IsCompact (ClockSection (completedReach W) τ) ∧
      ∃ M : ℝ, 0 < M ∧ ∀ v ∈ completedReach W, ‖v‖ ≤ M * τ v := by
  have weak := weak_clock_extends_to_completedReach W τ original_nonnegative
  have rest : ∀ h v, v ∈ completedReach W → ρ h v ∈ completedReach W := by
    intro h
    let f : V →L[ℝ] V :=
      { toLinearMap := ρ h, cont := (ρ h).continuous_of_finiteDimensional }
    exact increment_map_preserves_completedReach W f (original_rest_comparisons h)
  have positive := positive_clock_of_finite_rest_action
    (completedReach W) (zero_mem_completedReach W)
    (fun u hu v hv => add_mem_completedReach W hu hv)
    completed_order τ.toLinearMap weak ρ rest clock_preservation no_fixed_spatial
  obtain ⟨w, hw, hzero⟩ := occupied
  have nonzero : ∃ v ∈ completedReach W, v ≠ 0 :=
    ⟨w, original_mem_completedReach W hw, hzero⟩
  have conic : ∀ r : ℝ, 0 ≤ r → ∀ v ∈ completedReach W,
      r • v ∈ completedReach W :=
    fun r hr v hv => smul_mem_completedReach W r hr hv
  exact ⟨positive, clock_section_nonempty _ conic τ positive nonzero,
    clock_section_compact _ isClosed_closure conic τ positive,
    finite_comparison_bound _ isClosed_closure conic τ positive⟩

#print axioms original_mem_completedReach
#print axioms finiteReach_iff_original_ledger
#print axioms add_mem_completedReach
#print axioms smul_mem_completedReach
#print axioms weak_clock_extends_to_completedReach
#print axioms increment_map_preserves_completedReach
#print axioms source_increments_construct_compact_clock_section

end AASCMetricConstruction
