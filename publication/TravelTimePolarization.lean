import SROccupiedRayReach
import Mathlib.Analysis.InnerProductSpace.OfNorm

/-! Four earliest-arrival readings distinguish quadratic and nonquadratic
spatial geometry on the reciprocal homogeneous normed ray preparation.
The observed additions, the time unit and the spatial operands stay fixed. -/

namespace AASCMetricConstruction

noncomputable section
set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- All comparisons use the same four displacement requests. -/
def travelTimeParallelogram (τ : E → ℝ) : Prop :=
  ∀ x y, τ (x + y) ^ 2 + τ (x - y) ^ 2 = 2 * (τ x ^ 2 + τ y ^ 2)

/-- The original finite ray ledger supplies a least arrival at each displacement. -/
theorem sr_original_ray_least_arrival [Nontrivial E] (x : E) :
    IsLeast {t : ℝ | FiniteReach srOriginalFutureRayIncrements (t, x)} ‖x‖ := by
  constructor
  · apply (sr_original_ray_finite_reach_exact_full_cone _).mpr
    change ‖x‖ ≤ ‖x‖
    exact le_rfl
  · intro t ht
    exact (sr_original_ray_finite_reach_exact_full_cone _).mp ht

/-- The sum and difference arrival readings determine the mixed value of
a rival symmetric bilinear response on a given pair of displacements. -/
theorem sr_travel_time_polarization
    (τ : E → ℝ) (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (symm : ∀ u v, B u v = B v u)
    (x y : E) (plus : B (x+y) (x+y) = τ (x+y)^2)
    (minus : B (x-y) (x-y) = τ (x-y)^2) :
    B x y = (τ (x+y)^2 - τ (x-y)^2)/4 := by
  rw [← plus, ← minus]
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, symm y x]
  ring

/-- A failed parallelogram comparison precludes even a nonsymmetric
bilinear assignment agreeing on all four diagonal readings. -/
theorem sr_four_arrivals_exclude_bilinear_diagonal
    (τ : E → ℝ) (x y : E)
    (fails : τ (x+y)^2 + τ (x-y)^2 ≠ 2 * (τ x^2 + τ y^2)) :
    ¬ ∃ B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ,
      B x x = τ x^2 ∧ B y y = τ y^2 ∧
      B (x+y) (x+y) = τ (x+y)^2 ∧ B (x-y) (x-y) = τ (x-y)^2 := by
  rintro ⟨B, hx, hy, hp, hm⟩
  apply fails
  rw [← hx, ← hy, ← hp, ← hm]
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  ring

/-- An independently observed earliest-time function on the original rays
has a unique positive-definite symmetric bilinear realization if and only
if all its parallelogram comparisons pass. No spatial inner product is an
input. The data include the travel norm, not a comparison-group action. -/
theorem sr_original_earliest_times_determine_unique_spatial_form [Nontrivial E]
    (τ : E → ℝ)
    (earliest : ∀ x, IsLeast {t : ℝ | FiniteReach srOriginalFutureRayIncrements (t, x)} (τ x)) :
    travelTimeParallelogram τ ↔
      ∃! B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ,
        (∀ x y, B x y = B y x) ∧ (∀ x, x ≠ 0 → 0 < B x x) ∧
        (∀ x, B x x = τ x ^ 2) := by
  have times (x : E) : τ x = ‖x‖ := (earliest x).unique (sr_original_ray_least_arrival x)
  constructor
  · intro hp
    letI : InnerProductSpace ℝ E := InnerProductSpace.ofNorm (𝕜 := ℝ) (fun x y => by
      simpa only [times, pow_two] using hp x y)
    have symm (x y : E) : innerₗ E x y = innerₗ E y x := by
      simpa only [innerₗ_apply_apply] using real_inner_comm y x
    have diag (x : E) : innerₗ E x x = τ x ^ 2 := by
      rw [times, innerₗ_apply_apply, real_inner_self_eq_norm_sq]
    refine ⟨innerₗ E, ⟨symm, ?_, diag⟩, ?_⟩
    · intro x hx
      rw [diag, times]
      exact pow_pos (norm_pos_iff.mpr hx) 2
    · rintro B ⟨hs, _, hd⟩
      ext x y
      exact (sr_travel_time_polarization τ B hs x y (hd _) (hd _)).trans
        (sr_travel_time_polarization τ (innerₗ E) symm x y (diag _) (diag _)).symm
  · rintro ⟨B, ⟨_, _, hd⟩, _⟩ x y
    by_contra h
    exact sr_four_arrivals_exclude_bilinear_diagonal τ x y h
      ⟨B, hd x, hd y, hd _, hd _⟩

/-- The unique spatial form recovers the entire original finite and completed
reach relation as the future cone of the corresponding spacetime interval. -/
theorem sr_quadratic_travel_recovers_original_future [Nontrivial E]
    (τ : E → ℝ)
    (earliest : ∀ x, IsLeast {t : ℝ | FiniteReach srOriginalFutureRayIncrements (t, x)} (τ x))
    (records : travelTimeParallelogram τ) :
    ∃ B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ,
      (∀ x y, B x y = B y x) ∧ (∀ x, x ≠ 0 → 0 < B x x) ∧
      (∀ x, B x x = τ x^2) ∧ ∀ t x,
        (FiniteReach srOriginalFutureRayIncrements (t,x) ↔ 0 ≤ t ∧ 0 ≤ t^2 - B x x) ∧
        ((t,x) ∈ completedReach srOriginalFutureRayIncrements ↔ 0 ≤ t ∧ 0 ≤ t^2 - B x x) := by
  obtain ⟨B, ⟨hs, hpos, hd⟩, _⟩ :=
    (sr_original_earliest_times_determine_unique_spatial_form τ earliest).mp records
  refine ⟨B, hs, hpos, hd, fun t x => ?_⟩
  have ht := (earliest x).unique (sr_original_ray_least_arrival x)
  rw [sr_original_ray_finite_reach_exact_full_cone,
    sr_original_ray_completed_reach_exact_full_cone, and_self, hd x, ht]
  change ‖x‖ ≤ t ↔ 0 ≤ t ∧ 0 ≤ t^2 - ‖x‖^2
  constructor
  · intro h
    have h0 := (norm_nonneg x).trans h
    exact ⟨h0, sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg x) h0).mpr h)⟩
  · rintro ⟨h0, hq⟩
    exact (sq_le_sq₀ (norm_nonneg x) h0).mp (sub_nonneg.mp hq)

/-- Any admitted spatial linear comparison preserving all original
arrival records preserves the reconstructed mixed readings. This says
what follows for comparisons that are admitted, irrespective of which
physical comparisons the preparation actually supplies. -/
theorem sr_original_reach_transport_preserves_spatial_form [Nontrivial E]
    (A : E →ₗ[ℝ] E)
    (transport : ∀ t x, FiniteReach srOriginalFutureRayIncrements (t, A x) ↔
      FiniteReach srOriginalFutureRayIncrements (t, x))
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (symm : ∀ u v, B u v = B v u)
    (diagonal : ∀ x, B x x = ‖x‖^2) (x y : E) :
    B (A x) (A y) = B x y := by
  have preserves (z : E) : ‖A z‖ = ‖z‖ := by
    have eq : {t : ℝ | FiniteReach srOriginalFutureRayIncrements (t,A z)} =
        {t : ℝ | FiniteReach srOriginalFutureRayIncrements (t,z)} :=
      Set.ext fun t => transport t z
    have least := sr_original_ray_least_arrival (A z)
    rw [eq] at least
    exact least.unique (sr_original_ray_least_arrival z)
  have polar (u v : E) := sr_travel_time_polarization (fun z : E => ‖z‖)
    B symm u v (diagonal _) (diagonal _)
  rw [polar (A x) (A y), polar x y, ← A.map_add, ← A.map_sub]
  simp only [preserves]

/-- A cubic one-tick body has two unit coordinate displacements with unit
sum and difference. In the same records the two sides are 2 and 4. -/
theorem sr_cube_four_arrival_readings :
    ∃ x y : ℝ × ℝ × ℝ, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧ ‖x+y‖ = 1 ∧ ‖x-y‖ = 1 ∧
      ‖x+y‖^2 + ‖x-y‖^2 ≠ 2 * (‖x‖^2 + ‖y‖^2) := by
  refine ⟨(1, 0, 0), (0, 1, 0), ?_⟩
  norm_num [Prod.norm_def, Real.norm_eq_abs, Prod.fst_add, Prod.snd_add,
    Prod.fst_sub, Prod.snd_sub]

/-- Even the four indicated native readings on the cube defeat every
bilinear spatial form, on their original additive displacement carrier. -/
theorem sr_cube_admits_no_spatial_form :
    ¬ ∃ B : (ℝ × ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ) →ₗ[ℝ] ℝ, ∀ x, B x x = ‖x‖^2 := by
  obtain ⟨x, y, _, _, _, _, h⟩ := sr_cube_four_arrival_readings
  rintro ⟨B, hd⟩
  exact sr_four_arrivals_exclude_bilinear_diagonal (fun z => ‖z‖) x y h
    ⟨B, hd x, hd y, hd _, hd _⟩

/-- The *same* cubic carrier passes the six-event access experiment and
fails the test for a spatial quadratic form. The dispatches are at time
zero, their paired receivers are at the antipodes at time one. -/
theorem sr_cube_passes_six_events_without_quadratic_travel :
    (∃ s : Fin 3 → ℝ × ℝ × ℝ, ∀ i j : Fin 3,
      (FiniteReach srOriginalFutureRayIncrements (1, -s j - s i) ↔ i ≠ j) ∧
      ((1, -s j - s i) ∈ completedReach srOriginalFutureRayIncrements ↔ i ≠ j)) ∧
    ¬ ∃ B : (ℝ × ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ) →ₗ[ℝ] ℝ, ∀ x, B x x = ‖x‖^2 := by
  refine ⟨?_, sr_cube_admits_no_spatial_form⟩
  let s : Fin 3 → ℝ × ℝ × ℝ := ![(1,0,0),(-1,0,0),(0,1,0)]
  refine ⟨s, fun i j => ?_⟩
  rw [sr_original_ray_finite_reach_exact_full_cone,
    sr_original_ray_completed_reach_exact_full_cone, and_self]
  change ‖-s j - s i‖ ≤ 1 ↔ i ≠ j
  fin_cases i <;> fin_cases j <;>
    norm_num [s, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg,
      Real.norm_eq_abs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

end
end AASCMetricConstruction
