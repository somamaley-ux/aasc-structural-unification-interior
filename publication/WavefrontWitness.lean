import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-! Finite synchronous launch and receiver tests. An arrival reading is compared
to an inclusive deadline on the original clock. The operational criterion takes
the arrival readings from the source. The normed propagation specialization
constructs witnesses on any real normed plane, for its own propagation norm. -/
namespace AASCWavefront

set_option autoImplicit false
open scoped BigOperators

private theorem finite_margin {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (lo : A → ℝ) (hi : B → ℝ) (gap : ∀ i j, lo i < hi j) :
    ∃ t δ : ℝ, 0 < δ ∧ (∀ i, lo i ≤ t - δ) ∧ (∀ j, t + δ ≤ hi j) := by
  classical
  obtain ⟨i, _, high⟩ := Finset.exists_max_image Finset.univ lo Finset.univ_nonempty
  obtain ⟨j, _, low⟩ := Finset.exists_min_image Finset.univ hi Finset.univ_nonempty
  refine ⟨(lo i + hi j) / 2, (hi j - lo i) / 2, by linarith [gap i j], ?_, ?_⟩
  · intro k
    linarith [high k (Finset.mem_univ _)]
  · intro k
    linarith [low k (Finset.mem_univ _)]

/-- With an independently adjustable deadline at each receiver, start j can be
omitted exactly when a receiver sees it arrive strictly after all the others. -/
theorem receiver_deadlines_iff_strict_farthest
    {I R : Type*} [Fintype I] [Nontrivial I] (arrival : I → R → ℝ) :
    (∃ receiver : I → R, ∃ deadline : I → ℝ,
      ∀ i j, arrival i (receiver j) ≤ deadline j ↔ i ≠ j) ↔
    ∀ j : I, ∃ r : R, ∀ i, i ≠ j → arrival i r < arrival j r := by
  classical
  constructor
  · rintro ⟨receiver, deadline, pattern⟩ j
    exact ⟨receiver j, fun i h => ((pattern i j).mpr h).trans_lt
      (lt_of_not_ge fun le => (pattern j j).mp le rfl)⟩
  · intro cells
    choose r largest using cells
    have cut (j : I) : ∃ t : ℝ, ∀ i, arrival i (r j) ≤ t ↔ i ≠ j := by
      letI : Nonempty {i : I // i ≠ j} := ⟨⟨(exists_ne j).choose, (exists_ne j).choose_spec⟩⟩
      obtain ⟨t, δ, pos, lo, hi⟩ := finite_margin
        (fun i : {i : I // i ≠ j} => arrival i (r j)) (fun _ : Unit => arrival j (r j))
        (fun i _ => largest j i i.2)
      refine ⟨t, fun i => ⟨?_, ?_⟩⟩
      · rintro h rfl
        linarith [hi ()]
      · intro h
        linarith [lo ⟨i, h⟩]
    choose t h using cut
    exact ⟨r, t, fun i j => h j i⟩

/-- For a single synchronized deadline on given receivers the gap must hold
between every off-diagonal arrival and every diagonal arrival. -/
theorem common_deadline_iff {I : Type*} [Fintype I] [Nontrivial I] (a : I → I → ℝ) :
    (∃ t : ℝ, ∀ i j, a i j ≤ t ↔ i ≠ j) ↔
      ∀ i j, i ≠ j → ∀ k, a i j < a k k := by
  classical
  constructor
  · rintro ⟨t, p⟩ i j ij k
    exact ((p i j).mpr ij).trans_lt (lt_of_not_ge fun le => (p k k).mp le rfl)
  · intro gap
    obtain ⟨i, j, ij⟩ := exists_pair_ne I
    letI : Nonempty {p : I × I // p.1 ≠ p.2} := ⟨⟨(i,j), ij⟩⟩
    obtain ⟨t, δ, pos, lo, hi⟩ := finite_margin
      (fun p : {p : I × I // p.1 ≠ p.2} => a p.val.1 p.val.2) (fun k => a k k)
      (fun p k => gap p.val.1 p.val.2 p.2 k)
    refine ⟨t, fun i j => ⟨?_, ?_⟩⟩
    · rintro h rfl
      linarith [hi i]
    · intro ij
      linarith [lo ⟨(i,j), ij⟩]

/-- With interval-valued travel observations, a deadline certifies the pattern
for every compatible arrival table exactly at these two endpoint inequalities.
Arrival at the deadline counts as a hit. -/
theorem deadline_under_interval_uncertainty
    {I : Type*} (L U : I → I → ℝ) (bounds : ∀ i j, L i j ≤ U i j) (t : ℝ) :
    (∀ a : I → I → ℝ, (∀ i j, L i j ≤ a i j ∧ a i j ≤ U i j) →
      ∀ i j, a i j ≤ t ↔ i ≠ j) ↔
      (∀ i j, i ≠ j → U i j ≤ t) ∧ (∀ i, t < L i i) := by
  constructor
  · intro all
    have upper := all U (fun i j => ⟨bounds i j, le_rfl⟩)
    have lower := all L (fun i j => ⟨le_rfl, bounds i j⟩)
    exact ⟨fun i j ij => (upper i j).mpr ij,
      fun i => lt_of_not_ge fun le => (lower i i).mp le rfl⟩
  · rintro ⟨upper, lower⟩ a legal i j
    constructor
    · rintro le rfl
      exact (lower i).not_ge ((legal i i).1.trans le)
    · intro ij
      exact (legal i j).2.trans (upper i j ij)

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem double_norm (x : E) : ‖x + x‖ = 2 * ‖x‖ := by
  rw [← two_smul ℝ x, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

/-- A flat chord of the unit sphere gives a unit midpoint and a transverse
unit vector with both triangle inequalities strict. -/
private theorem directions_from_chord (x y : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (different : x ≠ y) (flat : ‖x + y‖ = 2) :
    ∃ u v : E, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ ‖u + v‖ < 2 ∧ ‖u - v‖ < 2 := by
  let d := ‖x - y‖
  have dpos : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr different)
  have dmax : d ≤ 2 := by
    calc d ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
         _ = 2 := by rw [hx, hy]; norm_num
  let u : E := (1/2 : ℝ) • (x+y)
  let v : E := d⁻¹ • (x-y)
  have hu : ‖u‖ = 1 := by
    dsimp only [u]
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2), flat]
    norm_num
  have hv : ‖v‖ = 1 := by
    dsimp only [v]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr dpos.le)]
    exact inv_mul_cancel₀ dpos.ne'
  have shift : (d/2) • v = (1/2 : ℝ) • (x-y) := by
    dsimp only [v]
    rw [smul_smul]
    congr 1
    field_simp
  have xp : u + (d/2) • v = x := by rw [shift]; dsimp [u]; module
  have yp : u - (d/2) • v = y := by rw [shift]; dsimp [u]; module
  have remainder : ‖(1-d/2) • v‖ = 1-d/2 := by
    rw [norm_smul, Real.norm_of_nonneg (by linarith), hv, mul_one]
  refine ⟨u, v, hu, hv, ?_, ?_⟩
  · have h : u + v = x + (1-d/2) • v := by rw [← xp]; module
    rw [h]
    have bound := norm_add_le x ((1-d/2) • v)
    rw [hx, remainder] at bound
    linarith
  · have h : u - v = y - (1-d/2) • v := by rw [← yp]; module
    rw [h]
    have bound := norm_sub_le y ((1-d/2) • v)
    rw [hy, remainder] at bound
    linarith

/-- Two non-antipodal distinct unit directions suffice, for any real norm. -/
theorem two_short_diagonals (x y : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (different : x ≠ y) (not_opposite : x ≠ -y) :
    ∃ u v : E, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ ‖u + v‖ < 2 ∧ ‖u - v‖ < 2 := by
  have plus : ‖x+y‖ ≤ 2 := by simpa only [hx, hy, one_add_one_eq_two] using norm_add_le x y
  have minus : ‖x-y‖ ≤ 2 := by simpa only [hx, hy, one_add_one_eq_two] using norm_sub_le x y
  rcases lt_or_eq_of_le plus with h | h
  · rcases lt_or_eq_of_le minus with h' | h'
    · exact ⟨x,y,hx,hy,h,h'⟩
    · exact directions_from_chord x (-y) hx ((norm_neg _).trans hy) not_opposite
        (by simpa only [sub_eq_add_neg] using h')
  · exact directions_from_chord x y hx hy different h

/-- Three equal-radius launches and their antipodal receivers exhibit the
three-by-three standard order pattern, with one common positive deadline.
This uses actual reversible norm-travel and the chosen events' availability. -/
theorem six_events_of_two_directions (x y : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (different : x ≠ y) (not_opposite : x ≠ -y) :
    ∃ s : Fin 3 → E, (∀ i, ‖s i‖ = 1) ∧ ∃ t : ℝ, 0 < t ∧ t < 2 ∧
      ∀ i j, ‖-s j - s i‖ ≤ t ↔ i ≠ j := by
  obtain ⟨u,v,hu,hv,plus,minus⟩ := two_short_diagonals x y hx hy different not_opposite
  let s : Fin 3 → E := ![u,-u,v]
  have unit (i : Fin 3) : ‖s i‖ = 1 := by fin_cases i <;> simp [s, hu, hv]
  have cost (i j : Fin 3) : ‖-s j-s i‖ = ‖s j+s i‖ := by
    rw [show -s j-s i = -(s j+s i) from by abel, norm_neg]
  have diag (i : Fin 3) : ‖-s i-s i‖ = 2 := by
    rw [cost, double_norm, unit, mul_one]
  have back : ‖v - u‖ < 2 := by simpa only [norm_sub_rev] using minus
  have off (i j : Fin 3) (ij : i ≠ j) : ‖-s j-s i‖ < 2 := by
    rw [cost]
    fin_cases i <;> fin_cases j <;>
      simp_all [s, sub_eq_add_neg, add_comm]
  obtain ⟨t, patt⟩ := (common_deadline_iff (fun i j => ‖-s j-s i‖)).mpr
    (fun i j ij k => (off i j ij).trans_eq (diag k).symm)
  have tnonneg := (norm_nonneg _).trans ((patt 0 1).mpr (by decide))
  have tmax : t < 2 := by
    rw [← diag 0]
    exact lt_of_not_ge fun h => (patt 0 0).mp h rfl
  refine ⟨s, unit, (t+2)/2, by linarith, by linarith, fun i j => ⟨?_, ?_⟩⟩
  · rintro le rfl
    rw [diag] at le
    linarith
  · intro ij
    linarith [(patt i j).mpr ij]

end Normed
end AASCWavefront
