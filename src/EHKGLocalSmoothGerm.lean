import EHKGCurvedOperand

/-! Compact localization preserves an exact smooth germ and a uniform bound.
The input is local smooth mathematics, never an evolution certificate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

theorem exists_compact_bounded_smooth_germ
    (f : CoordinatePoint → ℝ) (U : Set CoordinatePoint) (openU : IsOpen U)
    (zeroU : (0 : CoordinatePoint) ∈ U) (smooth : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (atZero : f 0 = 0) (delta : ℝ) (positive : 0 < delta) :
    ∃ h : ScalarSourceProbe (⊤ : Opens CoordinatePoint),
      (h : CoordinatePoint → ℝ) =ᶠ[𝓝 0] f ∧ ∀ p, |h p| ≤ delta / 2 := by
  have localSmooth := smooth.contDiffAt (openU.mem_nhds zeroU)
  have small : {p : CoordinatePoint | |f p| < delta / 2} ∈ 𝓝 0 := by
    apply (localSmooth.continuousAt.abs).eventually_lt continuousAt_const
    simpa [atZero] using (half_pos positive)
  obtain ⟨radius, radiusPos, inside⟩ :=
    Metric.mem_nhds_iff.mp (inter_mem (openU.mem_nhds zeroU) small)
  let bump : ContDiffBump (0 : CoordinatePoint) :=
    ⟨radius / 4, radius / 2, by positivity, by linarith⟩
  have supported (p : CoordinatePoint) (hp : p ∈ tsupport bump) :
      p ∈ U ∧ |f p| < delta / 2 := by
    apply inside
    rw [bump.tsupport_eq, Metric.mem_closedBall] at hp
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt hp (by dsimp [bump]; linarith)
  let localized : CoordinatePoint → ℝ := fun p => bump p * f p
  have smoothLocal : ContDiff ℝ (⊤ : ℕ∞) localized := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p ∈ tsupport bump
    · exact bump.contDiff.contDiffAt.mul
        (smooth.contDiffAt (openU.mem_nhds (supported p hp).1))
    · have near : localized =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) := by
        filter_upwards [(isClosed_tsupport (bump : CoordinatePoint → ℝ)).isOpen_compl.mem_nhds hp] with q hq
        simp only [localized, image_eq_zero_of_notMem_tsupport hq, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq near
  let h : ScalarSourceProbe (⊤ : Opens CoordinatePoint) :=
    ⟨localized, smoothLocal, bump.hasCompactSupport.mul_right, fun _ _ => Set.mem_univ _⟩
  refine ⟨h, ?_, ?_⟩
  · filter_upwards [bump.eventuallyEq_one] with p hp
    change bump p * f p = f p
    rw [hp, Pi.one_apply, one_mul]
  · intro p
    change |bump p * f p| ≤ delta / 2
    by_cases hp : p ∈ tsupport bump
    · calc
        |bump p * f p| = |bump p| * |f p| := abs_mul _ _
        _ ≤ 1 * |f p| := mul_le_mul_of_nonneg_right
          (by rw [abs_of_nonneg bump.nonneg]; exact bump.le_one) (abs_nonneg _)
        _ ≤ delta / 2 := by simpa using (supported p hp).2.le
    · rw [image_eq_zero_of_notMem_tsupport hp, zero_mul, abs_zero]
      exact (half_pos positive).le

end AASCKleinGordon.CurvedKG
