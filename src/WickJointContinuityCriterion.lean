import WickSchwartzSeminormBounds

noncomputable section
open Filter Topology
namespace AASCKleinGordon

variable {X Y Z : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [AddCommGroup Z] [Module ℝ Z] [TopologicalSpace Z]
  [IsTopologicalAddGroup Z]

/-- Joint continuity from a genuine continuous-seminorm product bound, using
all three additive laws. Fixed-state continuity alone is not used. -/
theorem wick_joint_sesq_test_continuous
    (B : X →ₗ⋆[ℂ] Y →ₗ[ℂ] (Z →L[ℝ] ℂ))
    (P : Seminorm ℂ X) (Q : Seminorm ℂ Y) (q : Z → ℝ)
    (hP : Continuous P) (hQ : Continuous Q) (hq : Continuous q) (hq0 : q 0=0)
    (hb : ∀ x y z,‖B x y z‖≤P x*Q y*q z) :
    Continuous (fun z : (X × Y) × Z => B z.1.1 z.1.2 z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  let G : (X × Y) × Z → ℝ := fun z =>
    P (z.1.1-z₀.1.1)*Q z.1.2*q z.2+
      P z₀.1.1*Q (z.1.2-z₀.1.2)*q z.2+
        P z₀.1.1*Q z₀.1.2*q (z.2-z₀.2)
  have hG : Continuous G := by
    dsimp only [G]
    fun_prop
  have hG0 : G z₀=0 := by simp [G,hq0]
  have hbound (z : (X × Y) × Z) :
      ‖B z.1.1 z.1.2 z.2-B z₀.1.1 z₀.1.2 z₀.2‖≤G z := by
    have he : B z.1.1 z.1.2 z.2-B z₀.1.1 z₀.1.2 z₀.2=
        B (z.1.1-z₀.1.1) z.1.2 z.2+B z₀.1.1 (z.1.2-z₀.1.2) z.2+
          B z₀.1.1 z₀.1.2 (z.2-z₀.2) := by
      simp only [map_sub,LinearMap.sub_apply,ContinuousLinearMap.sub_apply]
      abel
    rw [he]
    calc
      _ ≤ (‖B (z.1.1-z₀.1.1) z.1.2 z.2‖+‖B z₀.1.1 (z.1.2-z₀.1.2) z.2‖)+
          ‖B z₀.1.1 z₀.1.2 (z.2-z₀.2)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := add_le_add (add_le_add (hb _ _ _) (hb _ _ _)) (hb _ _ _)
  change Tendsto (fun z : (X × Y) × Z => B z.1.1 z.1.2 z.2)
    (𝓝 z₀) (𝓝 (B z₀.1.1 z₀.1.2 z₀.2))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hs : ∀ᶠ z in 𝓝 z₀,G z<ε := (hG.tendsto z₀).eventually
    (Iio_mem_nhds (by rw [hG0];exact hε))
  filter_upwards [hs] with z hz
  rw [dist_eq_norm]
  exact (hbound z).trans_lt hz

end AASCKleinGordon
