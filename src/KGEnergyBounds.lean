import KGMassShell

/-! Exact scalar inequalities used by current Module B's explicit Wigner
contraction. These are continuum momentum formulas, with no discretization.
They do not assert common-core or strong operator convergence. -/
noncomputable section
namespace AASCKleinGordon

theorem energy_ge_rest (a : Parameters) (p : Momentum) :
    a.mass*a.speed^2 ≤ energy a p := by
  have he := energy_sq a p
  have hp := momentumSq_nonneg p
  have hr : 0 < a.mass*a.speed^2 := mul_pos a.mass_pos (sq_pos_of_pos a.speed_pos)
  have hE := energy_pos a p
  nlinarith [mul_nonneg (sq_nonneg a.speed) hp]

theorem rest_subtracted_energy_rationalized (a : Parameters) (p : Momentum) :
    energy a p-a.mass*a.speed^2=
      a.speed^2*momentumSq p/(energy a p+a.mass*a.speed^2) := by
  have hd : energy a p+a.mass*a.speed^2≠0 := by
    have hE := energy_pos a p
    have hm := a.mass_pos
    positivity
  apply (eq_div_iff hd).2
  nlinarith [energy_sq a p]

theorem rest_subtracted_energy_bounds (a : Parameters) (p : Momentum) :
    0 ≤ energy a p-a.mass*a.speed^2 ∧
      energy a p-a.mass*a.speed^2 ≤ momentumSq p/(2*a.mass) := by
  have hE := energy_ge_rest a p
  refine ⟨sub_nonneg.2 hE,?_⟩
  have hc : 0 < a.speed^2 := sq_pos_of_pos a.speed_pos
  have hd : 0 < 2*a.mass := by have := a.mass_pos; positivity
  apply (le_div_iff₀ hd).2
  have hpoly : a.speed^2*(momentumSq p-(energy a p-a.mass*a.speed^2)*(2*a.mass)) =
      (energy a p-a.mass*a.speed^2)^2 := by nlinarith [energy_sq a p]
  have hn : 0 ≤ momentumSq p-(energy a p-a.mass*a.speed^2)*(2*a.mass) := by
    apply (mul_nonneg_iff_of_pos_left hc).1
    rw [hpoly]
    positivity
  linarith

theorem exact_kinetic_error (a : Parameters) (p : Momentum) :
    momentumSq p/(2*a.mass)-(energy a p-a.mass*a.speed^2)=
      (energy a p-a.mass*a.speed^2)^2/(2*a.mass*a.speed^2) := by
  have hm : a.mass≠0 := ne_of_gt a.mass_pos
  have hc : a.speed≠0 := ne_of_gt a.speed_pos
  field_simp
  nlinarith [energy_sq a p]

theorem wigner_weight_cancels_boost_coefficient (a : Parameters) (p : Momentum) :
    (a.mass*a.speed^2/energy a p)*(energy a p/a.speed^2)=a.mass := by
  have hE : energy a p≠0 := ne_of_gt (energy_pos a p)
  have hc : a.speed≠0 := ne_of_gt a.speed_pos
  field_simp

end AASCKleinGordon
