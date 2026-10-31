import SchwartzCutoffConstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Filter Topology
open scoped SchwartzMap
namespace AASCKleinGordon
attribute [local irreducible] wickSchwartzLocalize

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def wickLocalizationControl (f : 𝓢(E,ℂ)) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1),(n.choose i : ℝ)*
    SchwartzMap.seminorm ℂ 0 i (wickLocalizationBase E)*SchwartzMap.seminorm ℂ k (n-i) f

theorem wick_localization_control_nonnegative (f : 𝓢(E,ℂ)) (k n : ℕ) :
    0≤wickLocalizationControl f k n := by
  unfold wickLocalizationControl
  apply Finset.sum_nonneg
  intro i _hi
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)) (apply_nonneg _ _)

theorem wick_schwartz_localize_uniform_seminorm_bound (R : ℝ) (hR : 0<R) (hR1 : 1≤R)
    (f : 𝓢(E,ℂ)) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (wickSchwartzLocalize R hR f)≤wickLocalizationControl f k n := by
  apply SchwartzMap.seminorm_le_bound ℂ k n _ (wick_localization_control_nonnegative f k n)
  intro x
  have hfun : (⇑(wickSchwartzLocalize R hR f) : E → ℂ)=
      fun y => wickLocalizationCutoff R hR y*f y := funext (wick_schwartz_localize_apply R hR f)
  rw [hfun]
  calc
    _ ≤ ‖x‖^k * ∑ i ∈ Finset.range (n+1),(n.choose i : ℝ)*
        ‖iteratedFDeriv ℝ i (wickLocalizationCutoff (E:=E) R hR) x‖*
          ‖iteratedFDeriv ℝ (n-i) f x‖ :=
      mul_le_mul_of_nonneg_left
        (norm_iteratedFDeriv_mul_le ((wickLocalizationCutoff R hR).smooth ⊤) (f.smooth ⊤) x
          (by exact_mod_cast le_top)) (by positivity)
    _ = ∑ i ∈ Finset.range (n+1),((n.choose i : ℝ)*
        ‖iteratedFDeriv ℝ i (wickLocalizationCutoff (E:=E) R hR) x‖)*
          (‖x‖^k*‖iteratedFDeriv ℝ (n-i) f x‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (wick_localization_cutoff_derivative_bound R hR hR1 i x)
          (Nat.cast_nonneg _))
        (SchwartzMap.le_seminorm ℂ k (n-i) f x) (by positivity)
        (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _))

/- A supported-away-from-the-origin derivative loses one weight with the
explicit inverse-radius estimate. No approximation hypothesis is received. -/
omit [FiniteDimensional ℝ E] in
theorem wick_schwartz_seminorm_tail_bound (R : ℝ) (hR : 0<R) (f : 𝓢(E,ℂ)) (k n : ℕ)
    (hz : ∀ x : E,‖x‖<R → iteratedFDeriv ℝ n f x=0) :
    SchwartzMap.seminorm ℂ k n f≤SchwartzMap.seminorm ℂ (k+1) n f/R := by
  apply SchwartzMap.seminorm_le_bound ℂ k n f (div_nonneg (apply_nonneg _ _) hR.le)
  intro x
  by_cases hx : ‖x‖<R
  · rw [hz x hx,norm_zero,mul_zero]
    exact div_nonneg (apply_nonneg _ _) hR.le
  · apply (le_div_iff₀ hR).mpr
    calc
      (‖x‖^k*‖iteratedFDeriv ℝ n f x‖)*R≤
          (‖x‖^k*‖iteratedFDeriv ℝ n f x‖)*‖x‖ :=
        mul_le_mul_of_nonneg_left (le_of_not_gt hx) (by positivity)
      _ = ‖x‖^(k+1)*‖iteratedFDeriv ℝ n f x‖ := by rw [pow_succ];ring
      _ ≤ _ := SchwartzMap.le_seminorm ℂ (k+1) n f x

def wickLocalizationErrorControl (f : 𝓢(E,ℂ)) (k n : ℕ) : ℝ :=
  wickLocalizationControl f (k+1) n+SchwartzMap.seminorm ℂ (k+1) n f

theorem wick_localization_error_control_nonnegative (f : 𝓢(E,ℂ)) (k n : ℕ) :
    0≤wickLocalizationErrorControl f k n :=
  add_nonneg (wick_localization_control_nonnegative f (k+1) n) (apply_nonneg _ _)

theorem wick_schwartz_cutoff_error_bound (R : ℝ) (hR : 0<R) (hR1 : 1≤R)
    (f : 𝓢(E,ℂ)) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (wickSchwartzLocalize R hR f-f)≤
      wickLocalizationErrorControl f k n/R := by
  have ht := wick_schwartz_seminorm_tail_bound R hR (wickSchwartzLocalize R hR f-f) k n
    (fun x hx => wick_schwartz_localize_error_jet_zero R hR f n hx)
  have hsub : SchwartzMap.seminorm ℂ (k+1) n (wickSchwartzLocalize R hR f-f)≤
      SchwartzMap.seminorm ℂ (k+1) n (wickSchwartzLocalize R hR f)+
        SchwartzMap.seminorm ℂ (k+1) n f :=
    map_sub_le_add (SchwartzMap.seminorm ℂ (k+1) n) (wickSchwartzLocalize R hR f) f
  have hb : SchwartzMap.seminorm ℂ (k+1) n (wickSchwartzLocalize R hR f-f)≤
      wickLocalizationControl f (k+1) n+SchwartzMap.seminorm ℂ (k+1) n f :=
    hsub.trans (add_le_add
      (wick_schwartz_localize_uniform_seminorm_bound R hR hR1 f (k+1) n) le_rfl)
  exact ht.trans (div_le_div_of_nonneg_right hb hR.le)

def wickSchwartzCutoffSequence (f : 𝓢(E,ℂ)) (N : ℕ) : 𝓢(E,ℂ) :=
  wickSchwartzLocalize ((N:ℝ)+1) (by positivity) f

theorem wick_schwartz_cutoff_sequence_compact (f : 𝓢(E,ℂ)) (N : ℕ) :
    HasCompactSupport (wickSchwartzCutoffSequence f N) := wick_schwartz_localize_support _ _ f

/-- Actual convergence in every Schwartz seminorm, not an Lp statement. -/
theorem wick_schwartz_cutoff_sequence_tendsto (f : 𝓢(E,ℂ)) :
    Tendsto (wickSchwartzCutoffSequence f) atTop (𝓝 f) := by
  apply ((schwartz_withSeminorms ℂ E ℂ).tendsto_nhds_atTop _ _).mpr
  rintro ⟨k,n⟩ ε hε
  obtain ⟨N,hN⟩ := exists_nat_gt (wickLocalizationErrorControl f k n/ε)
  refine ⟨N,?_⟩
  intro M hM
  have hNM : (N:ℝ)≤(M:ℝ) := by exact_mod_cast hM
  have hR : 0<(M:ℝ)+1 := by positivity
  have hsmall : wickLocalizationErrorControl f k n/((M:ℝ)+1)<ε := by
    apply (div_lt_iff₀ hR).mpr
    have hC : wickLocalizationErrorControl f k n<((M:ℝ)+1)*ε :=
      (div_lt_iff₀ hε).mp (hN.trans_le (by linarith))
    nlinarith
  exact (wick_schwartz_cutoff_error_bound ((M:ℝ)+1) hR
    (by linarith [Nat.cast_nonneg (α:=ℝ) M]) f k n).trans_lt hsmall

end AASCKleinGordon
