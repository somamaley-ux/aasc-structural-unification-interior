import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! Local additive rest readouts on their actual downward-closed domain.
Neither global continuation nor scalar homogeneity is an input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set
namespace AASCKleinGordon.OperationalSR

structure LocalRestLaw where
  domain : Set ℝ
  zero_mem : 0 ∈ domain
  domain_nonnegative : ∀ x ∈ domain, 0 ≤ x
  subdivision : ∀ x ∈ domain, ∀ y : ℝ, 0 ≤ y → y ≤ x → y ∈ domain
  response : ℝ → ℝ
  response_nonnegative : ∀ x ∈ domain, 0 ≤ response x
  response_add : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x+y ∈ domain →
    response (x+y) = response x+response y

theorem local_rest_response_zero (D : LocalRestLaw) : D.response 0 = 0 := by
  have h := D.response_add 0 0 (by norm_num) (by norm_num) (by simpa using D.zero_mem)
  simp only [zero_add] at h
  linarith

theorem local_rest_response_monotone (D : LocalRestLaw) : MonotoneOn D.response D.domain := by
  intro x hx y hy order
  have difference : y-x ∈ D.domain :=
    D.subdivision y hy (y-x) (sub_nonneg.mpr order) (by linarith [D.domain_nonnegative x hx])
  have add := D.response_add x (y-x) (D.domain_nonnegative x hx) (sub_nonneg.mpr order)
    (by simpa only [add_sub_cancel] using hy)
  rw [add_sub_cancel] at add
  linarith [D.response_nonnegative (y-x) difference]

theorem local_rest_response_nsmul (D : LocalRestLaw) (n : ℕ) (x : ℝ)
    (positive : 0 ≤ x) (inside : (n:ℝ)*x ∈ D.domain) :
    D.response ((n:ℝ)*x) = (n:ℝ)*D.response x := by
  induction n with
  | zero => simp [local_rest_response_zero]
  | succ n ih =>
    have previous : (n:ℝ)*x ∈ D.domain := D.subdivision _ inside _
      (mul_nonneg (Nat.cast_nonneg n) positive) (by push_cast; nlinarith)
    have add := D.response_add ((n:ℝ)*x) x
      (mul_nonneg (Nat.cast_nonneg n) positive) positive
      (by convert inside using 1 <;> push_cast <;> ring)
    rw [ih previous] at add
    convert add using 1 <;> push_cast <;> ring

theorem calibrated_rest_grid_error (D : LocalRestLaw) (T : ℝ)
    (positive : 0 < T) (calibratedDomain : T ∈ D.domain) (calibrated : D.response T=T)
    (r : ℝ) (inside : r ∈ D.domain) (n : ℕ) (hn : 0 < n) :
    |D.response r-r| ≤ T/(n:ℝ) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hnOne : (1:ℝ) ≤ n := by exact_mod_cast hn
  let u := T/(n:ℝ)
  have hu : 0 < u := div_pos positive hnR
  have uBound : u ≤ T := (div_le_iff₀ hnR).mpr (by nlinarith)
  have uInside := D.subdivision T calibratedDomain u hu.le uBound
  have gridTotal : (n:ℝ)*u=T := by dsimp [u];field_simp
  have grid := local_rest_response_nsmul D n u hu.le (by rw [gridTotal];exact calibratedDomain)
  rw [gridTotal,calibrated] at grid
  have unitResponse : D.response u=u := by
    apply mul_left_cancel₀ hnR.ne'
    exact grid.symm.trans gridTotal.symm
  let k := Nat.floor (r/u)
  have hr := D.domain_nonnegative r inside
  have lower : (k:ℝ)*u ≤ r := (le_div_iff₀ hu).mp (Nat.floor_le (div_nonneg hr hu.le))
  have upper : r < ((k:ℝ)+1)*u := (div_lt_iff₀ hu).mp (Nat.lt_floor_add_one (r/u))
  have lowerNonnegative : 0 ≤ (k:ℝ)*u := mul_nonneg (Nat.cast_nonneg k) hu.le
  have lowerInside := D.subdivision r inside ((k:ℝ)*u) lowerNonnegative lower
  let delta := r-(k:ℝ)*u
  have deltaNonnegative : 0 ≤ delta := sub_nonneg.mpr lower
  have deltaBound : delta ≤ u := by dsimp [delta];nlinarith
  have deltaInside := D.subdivision u uInside delta deltaNonnegative deltaBound
  have smallResponse : D.response delta ≤ u := by
    rw [←unitResponse]
    exact local_rest_response_monotone D deltaInside uInside deltaBound
  have split := D.response_add ((k:ℝ)*u) delta lowerNonnegative deltaNonnegative
    (by convert inside using 1 <;> dsimp [delta] <;> ring)
  have sum : (k:ℝ)*u+delta=r := by dsimp [delta];ring
  rw [sum,local_rest_response_nsmul D k u hu.le lowerInside,unitResponse] at split
  change |D.response r-r| ≤ u
  apply abs_le.mpr
  constructor <;> dsimp [delta] at * <;> nlinarith [D.response_nonnegative _ deltaInside]

theorem calibrated_local_rest_response_unique (D : LocalRestLaw) (T : ℝ)
    (positive : 0 < T) (calibratedDomain : T ∈ D.domain) (calibrated : D.response T=T)
    (r : ℝ) (inside : r ∈ D.domain) : D.response r=r := by
  have zero : |D.response r-r|=0 := by
    apply le_antisymm ?_ (abs_nonneg _)
    by_contra bad
    have hpos : 0 < |D.response r-r| := lt_of_not_ge bad
    obtain ⟨n,small⟩ := exists_nat_one_div_lt (div_pos hpos positive)
    have small' : T/(n+1:ℝ) < |D.response r-r| := by
      have multiplied := (lt_div_iff₀ positive).mp small
      convert multiplied using 1 <;> ring
    have bound := calibrated_rest_grid_error D T positive calibratedDomain calibrated r inside (n+1) (Nat.succ_pos n)
    push_cast at bound
    linarith
  exact sub_eq_zero.mp (abs_eq_zero.mp zero)

end AASCKleinGordon.OperationalSR
