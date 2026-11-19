import SRJointOriginalSource
import SROccupiedRayReach

/-! Six events distinguish the original three-space completed ray order
from the one-space order by a finite comparison experiment. -/
noncomputable section
set_option autoImplicit false
open AASCMetricConstruction AASCKleinGordon.CanonicalLicensing.SRIntegration
open scoped BigOperators

namespace AASCOrderObstruction

/-- A single ordered coordinate can reverse at most one diagonal. -/
private theorem one_reversal {X : Type*} [Preorder X] (a b : Fin 3 → X)
    (cross : ∀ i j, i ≠ j → a i ≤ b j)
    (i j : Fin 3) (ij : i ≠ j) (hi : b i < a i) (hj : b j < a j) : False :=
  (lt_irrefl (b i)) ((((hi.trans_le (cross i j ij)).trans hj).trans_le (cross j i ij.symm)))

theorem two_orders_exclude_three_diagonals {X Y : Type*} [LinearOrder X] [LinearOrder Y]
    (a b : Fin 3 → X × Y) : ¬ ∀ i j, a i ≤ b j ↔ i ≠ j := by
  intro pattern
  have diagonal (i : Fin 3) : (b i).1 < (a i).1 ∨ (b i).2 < (a i).2 := by
    by_contra! h
    exact (pattern i i).mp ⟨h.1,h.2⟩ rfl
  have left := one_reversal (fun i => (a i).1) (fun i => (b i).1)
    (fun i j hij => ((pattern i j).mpr hij).1)
  have right := one_reversal (fun i => (a i).2) (fun i => (b i).2)
    (fun i j hij => ((pattern i j).mpr hij).2)
  rcases diagonal 0 with l0 | r0 <;> rcases diagonal 1 with l1 | r1 <;>
    rcases diagonal 2 with l2 | r2 <;>
    first
    | exact left 0 1 (by decide) l0 l1
    | exact left 0 2 (by decide) l0 l2
    | exact left 1 2 (by decide) l1 l2
    | exact right 0 1 (by decide) r0 r1
    | exact right 0 2 (by decide) r0 r2
    | exact right 1 2 (by decide) r1 r2

def rayBefore {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (p q : ℝ × E) : Prop :=
  q-p ∈ completedReach srOriginalFutureRayIncrements

def nullCoordinates (p : ℝ × ℝ) : ℝ × ℝ := (p.1+p.2,p.1-p.2)

theorem one_space_order_iff_null_product (p q : ℝ × ℝ) :
    rayBefore p q ↔ nullCoordinates p ≤ nullCoordinates q := by
  rw [rayBefore,sr_original_ray_completed_reach_exact_full_cone]
  change ‖q.2-p.2‖ ≤ q.1-p.1 ↔ p.1+p.2 ≤ q.1+q.2 ∧ p.1-p.2 ≤ q.1-q.2
  rw [Real.norm_eq_abs,abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem no_six_one_space_events (a b : Fin 3 → ℝ × ℝ) :
    ¬ ∀ i j, rayBefore (a i) (b j) ↔ i ≠ j := by
  intro pattern
  apply two_orders_exclude_three_diagonals (fun i => nullCoordinates (a i))
    (fun j => nullCoordinates (b j))
  exact fun i j => (one_space_order_iff_null_product _ _).symm.trans (pattern i j)

def early (i : Fin 3) : SREvent := (0,EuclideanSpace.single i 1)
def late (i : Fin 3) : SREvent := (3/2,-EuclideanSpace.single i 1)

theorem six_native_events (i j : Fin 3) : rayBefore (early i) (late j) ↔ i ≠ j := by
  rw [rayBefore,sr_original_ray_completed_reach_exact_full_cone]
  let d : SRSpace := -(EuclideanSpace.single j 1) - (EuclideanSpace.single i 1)
  change ‖d‖ ≤ 3/2-0 ↔ i ≠ j
  have square : ‖d‖^2 = if i = j then 4 else 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;>
      norm_num [d,EuclideanSpace.single_apply,Pi.single_apply,
        PiLp.sub_apply,PiLp.neg_apply,Real.norm_eq_abs,Fin.ext_iff]
  by_cases h : i = j
  · simp [h] at square ⊢
    nlinarith [norm_nonneg d]
  · simp [h] at square ⊢
    nlinarith [norm_nonneg d]

theorem no_exact_event_map_to_one_space :
    ¬ ∃ F : SREvent → ℝ × ℝ, ∀ p q, rayBefore p q ↔ rayBefore (F p) (F q) := by
  rintro ⟨F,exactOrder⟩
  apply no_six_one_space_events (fun i => F (early i)) (fun j => F (late j))
  intro i j
  exact (exactOrder _ _).symm.trans (six_native_events i j)

theorem no_exact_event_cover_from_one_space :
    ¬ ∃ F : (ℝ × ℝ) → SREvent, Function.Surjective F ∧
      ∀ p q, rayBefore p q ↔ rayBefore (F p) (F q) := by
  rintro ⟨F,onto,exactOrder⟩
  choose sectionPoint sectionLaw using onto
  apply no_exact_event_map_to_one_space
  refine ⟨sectionPoint,fun p q => ?_⟩
  simpa only [sectionLaw] using (exactOrder (sectionPoint p) (sectionPoint q)).symm

end AASCOrderObstruction
