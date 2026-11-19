import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-! Exact signal arrival with a common real clock and a symmetric travel-time
distance. Arbitrary site/time preparations are available, and the closed
deadline test includes arrivals at the deadline. -/
namespace AASCPairMeetings

variable {X : Type*} [PseudoMetricSpace X]

def SixEventTest (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∃ x y : Fin 3 → X, ∃ s t : Fin 3 → ℝ, ∀ i j,
    (s i + dist (x i) (y j) ≤ t j ↔ i ≠ j)

def FourPoint (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ p q r u : X, dist p q + dist r u ≤
    max (dist p r + dist q u) (dist p u + dist q r)

/-- In a four-point delay geometry, a pair of maximal weighted separation
dominates the third arrival at every observer. -/
theorem pair_bounds_remaining_arrival (tree : FourPoint X)
    (p q r y : X) (s t u : ℝ)
    (h₁ : s + t + dist p q ≤ t + u + dist q r)
    (h₂ : s + u + dist p r ≤ t + u + dist q r) :
    s + dist p y ≤ max (t + dist q y) (u + dist r y) := by
  have h := tree p y q r
  rw [dist_comm y r, dist_comm y q] at h
  rcases le_total (dist p q + dist r y) (dist p r + dist q y) with hle | hle
  · rw [max_eq_right hle] at h
    apply le_trans _ (le_max_left _ _)
    linarith
  · rw [max_eq_left hle] at h
    apply le_trans _ (le_max_right _ _)
    linarith

theorem four_point_excludes_six_events (tree : FourPoint X) : ¬ SixEventTest X := by
  rintro ⟨x, y, s, t, obs⟩
  let w (i j : Fin 3) := s i + s j + dist (x i) (x j)
  have sym (i j : Fin 3) : w i j = w j i := by
    dsimp [w]
    rw [dist_comm (x j) (x i)]
    ring
  have kill (i j k : Fin 3) (ji : j ≠ i) (ki : k ≠ i)
      (h₁ : w i j ≤ w j k) (h₂ : w i k ≤ w j k) : False := by
    have bound := pair_bounds_remaining_arrival tree (x i) (x j) (x k) (y i)
      (s i) (s j) (s k) h₁ h₂
    have allEarly := max_le ((obs j i).mpr ji) ((obs k i).mpr ki)
    exact ((obs i i).mp (bound.trans allEarly)) rfl
  by_cases h : w 0 1 ≤ w 1 2
  · by_cases h' : w 0 2 ≤ w 1 2
    · exact kill 0 1 2 (by decide) (by decide) h h'
    · exact kill 1 0 2 (by decide) (by decide) (by rw [sym 1 0]; exact h.trans (le_of_not_ge h'))
        (le_of_not_ge h')
  · have h' := le_of_not_ge h
    by_cases g : w 0 2 ≤ w 0 1
    · exact kill 2 0 1 (by decide) (by decide) (by rw [sym 2 0]; exact g) (by rw [sym 2 1]; exact h')
    · exact kill 1 0 2 (by decide) (by decide) (by rw [sym 1 0]; exact le_of_not_ge g)
        (h'.trans (le_of_not_ge g))

/-- The six directed comparisons are reconstructed from six ordinary
pairwise travel times at four original sites. -/
theorem six_events_of_strict_four_point (p q r u : X)
    (split : max (dist p r + dist q u) (dist p u + dist q r) <
      dist p q + dist r u) : SixEventTest X := by
  let a := dist p q
  let b := dist p r
  let c := dist p u
  let d := dist q r
  let e := dist q u
  let f := dist r u
  let δ := (a + f - max (b + e) (c + d)) / 4
  have gap : max (b+e) (c+d) < a+f := split
  have pos : 0 < δ := by dsimp [δ]; linarith
  have be : b + e + 4*δ ≤ a + f := by dsimp [δ]; linarith [le_max_left (b+e) (c+d)]
  have cd : c + d + 4*δ ≤ a + f := by dsimp [δ]; linarith [le_max_right (b+e) (c+d)]
  have fe : f ≤ d + e := by simpa [f,d,e,dist_comm r q] using dist_triangle r q u
  have ab : a ≤ b + d := by simpa [a,b,d,dist_comm r q] using dist_triangle p r q
  let x : Fin 3 → X := ![p,q,r]
  let y : Fin 3 → X := ![q,r,u]
  let s : Fin 3 → ℝ := ![0,b-d+δ,a-d-δ]
  -- Each deadline is below its own missing arrival, with enough time
  -- for both of the other signals on their earliest routes.
  let t : Fin 3 → ℝ := ![a-δ, b, a-d-2*δ+f]
  refine ⟨x,y,s,t,?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [x,y,s,t,dist_comm r q] <;>
    dsimp only [a,b,c,d,e,f] at be cd fe ab ⊢ <;> linarith

theorem six_events_iff_not_four_point : SixEventTest X ↔ ¬ FourPoint X := by
  constructor
  · exact fun six tree => four_point_excludes_six_events tree six
  · intro h
    unfold FourPoint at h
    push_neg at h
    obtain ⟨p,q,r,u,split⟩ := h
    exact six_events_of_strict_four_point p q r u split

/-- Certified lower and upper bounds on the six original travel times suffice.
The four labels in this test need not exhaust the domain. -/
theorem six_events_from_certified_bounds (p q r u : X) (lo hi : X → X → ℝ)
    (pq : lo p q ≤ dist p q) (ru : lo r u ≤ dist r u)
    (pr : dist p r ≤ hi p r) (qu : dist q u ≤ hi q u)
    (pu : dist p u ≤ hi p u) (qr : dist q r ≤ hi q r)
    (gap : max (hi p r + hi q u) (hi p u + hi q r) < lo p q + lo r u) :
    SixEventTest X := by
  apply six_events_of_strict_four_point p q r u
  exact (max_le_max (add_le_add pr qu) (add_le_add pu qr)).trans_lt
    (gap.trans_le (add_le_add pq ru))

/-- A gap strictly exceeding four single-reading error bounds certifies the
same strict quartet for the original delays. -/
theorem six_events_from_measurements (p q r u : X) (m : X → X → ℝ) (err : ℝ)
    (accurate : ∀ x y, |m x y - dist x y| ≤ err)
    (observed : max (m p r + m q u) (m p u + m q r) + 4*err < m p q + m r u) :
    SixEventTest X := by
  apply six_events_from_certified_bounds p q r u
    (fun x y => m x y - err) (fun x y => m x y + err)
  · linarith [(abs_le.mp (accurate p q)).2]
  · linarith [(abs_le.mp (accurate r u)).2]
  · linarith [(abs_le.mp (accurate p r)).1]
  · linarith [(abs_le.mp (accurate q u)).1]
  · linarith [(abs_le.mp (accurate p u)).1]
  · linarith [(abs_le.mp (accurate q r)).1]
  · apply max_lt <;> linarith [le_max_left (m p r + m q u) (m p u + m q r),
      le_max_right (m p r + m q u) (m p u + m q r)]

end AASCPairMeetings
