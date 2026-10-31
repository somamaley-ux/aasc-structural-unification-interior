import EHKGDiamondCauchyLeaf

/-! Compact localization for arbitrary locally smooth comparison fields.
A finite family of actual smooth bumps constructs a global compact smooth
extension equal near the requested compact set. No PDE or evolution premise. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology BigOperators
namespace AASCKleinGordon.CurvedKG

theorem exists_compact_smooth_cutoff (K U : Set CoordinatePoint) (compactK : IsCompact K)
    (openU : IsOpen U) (inside : K ⊆ U) :
    ∃ beta : CoordinatePoint → ℝ, ContDiff ℝ (⊤ : ℕ∞) beta ∧ HasCompactSupport beta ∧
      tsupport beta ⊆ U ∧ ∀ p ∈ K, beta =ᶠ[𝓝 p] (fun _ => 1) := by
  classical
  have pointBump (p : K) : ∃ b : ContDiffBump p.val, tsupport (b : CoordinatePoint → ℝ) ⊆ U := by
    obtain ⟨r, positive, contained⟩ := Metric.mem_nhds_iff.mp (openU.mem_nhds (inside p.property))
    let b : ContDiffBump p.val := ⟨r / 4, r / 2, by positivity, by linarith⟩
    refine ⟨b, ?_⟩
    intro q hq
    apply contained
    rw [b.tsupport_eq, Metric.mem_closedBall] at hq
    change dist q p.val < r
    exact hq.trans_lt (by dsimp [b]; linarith)
  let b (p : K) : ContDiffBump p.val := Classical.choose (pointBump p)
  have supported (p : K) : tsupport (b p : CoordinatePoint → ℝ) ⊆ U := Classical.choose_spec (pointBump p)
  obtain ⟨cover, covers⟩ := compactK.elim_finite_subcover (fun p : K => Metric.ball p.val (b p).rIn)
    (fun _ => Metric.isOpen_ball) (by
      intro p hp
      exact mem_iUnion.mpr ⟨⟨p, hp⟩, Metric.mem_ball_self (b ⟨p, hp⟩).rIn_pos⟩)
  let I := {p : K // p ∈ cover}
  let beta : CoordinatePoint → ℝ := fun q => 1 - ∏ p : I, (1 - b p.val q)
  have smooth : ContDiff ℝ (⊤ : ℕ∞) beta :=
    contDiff_const.sub (contDiff_prod (fun p _ => contDiff_const.sub (b p.val).contDiff))
  let C : Set CoordinatePoint := ⋃ p : I, tsupport (b p.val : CoordinatePoint → ℝ)
  have compactC : IsCompact C := isCompact_iUnion (fun p : I => (b p.val).hasCompactSupport)
  have supportC : Function.support beta ⊆ C := by
    intro q hq
    by_contra absent
    have allZero (p : I) : b p.val q = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => absent (mem_iUnion.mpr ⟨p, h⟩))
    exact hq (by simp [beta, allZero])
  have tsupportC : tsupport beta ⊆ C := closure_minimal supportC compactC.isClosed
  refine ⟨beta, smooth, compactC.of_isClosed_subset (isClosed_tsupport beta) tsupportC, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp⟩ := mem_iUnion.mp (tsupportC hq)
    exact supported p.val hp
  · intro p hp
    obtain ⟨q, hq, nearby⟩ := mem_iUnion₂.mp (covers hp)
    let chosen : I := ⟨q, hq⟩
    filter_upwards [(b q).eventuallyEq_one_of_mem_ball nearby] with x hx
    have factor : (1 : ℝ) - b chosen.val x = 0 := by simpa only [Pi.one_apply, chosen, sub_self] using congrArg (fun y : ℝ => 1 - y) hx
    have productZero : (∏ i : I, ((1 : ℝ) - b i.val x)) = 0 :=
      Finset.prod_eq_zero_iff.mpr ⟨chosen, Finset.mem_univ _, factor⟩
    simp only [beta, productZero, sub_zero]

theorem exists_global_compact_smooth_localization (K U : Set CoordinatePoint)
    (compactK : IsCompact K) (openU : IsOpen U) (inside : K ⊆ U)
    (f : CoordinatePoint → ℝ) (smooth : ContDiffOn ℝ (⊤ : ℕ∞) f U) :
    ∃ F : CoordinatePoint → ℝ, ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧
      ∀ p ∈ K, F =ᶠ[𝓝 p] f := by
  obtain ⟨beta, regular, compact, supported, near⟩ := exists_compact_smooth_cutoff K U compactK openU inside
  let F : CoordinatePoint → ℝ := fun p => beta p * f p
  have globalSmooth : ContDiff ℝ (⊤ : ℕ∞) F := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p ∈ tsupport beta
    · exact regular.contDiffAt.mul (smooth.contDiffAt (openU.mem_nhds (supported hp)))
    · have zero : F =ᶠ[𝓝 p] (fun _ => 0) := by
        filter_upwards [(isClosed_tsupport beta).isOpen_compl.mem_nhds hp] with q hq
        simp only [F, image_eq_zero_of_notMem_tsupport hq, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq zero
  refine ⟨F, globalSmooth, compact.mul_right, ?_⟩
  intro p hp
  filter_upwards [near p hp] with q hq
  simp only [F, hq, one_mul]

end AASCKleinGordon.CurvedKG
