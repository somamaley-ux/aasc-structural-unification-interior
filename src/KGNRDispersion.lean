import WickIsolatedMassSector

/-! A controlled scalar, one-particle nonrelativistic limit of the retained
KG mass shell.  The mass and action anchors remain explicit physical inputs.
This analytic limit neither authorizes an interior nor identifies full Fock
evolution with nonrelativistic evolution. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Filter
namespace AASCKleinGordon

/-- Change only the admitted speed anchor of the original KG parameters. -/
def kgNRParameters (a : Parameters) (c : ℝ) (hc : 0 < c) : Parameters where
  mass := a.mass
  speed := c
  hbar := a.hbar
  mass_pos := a.mass_pos
  speed_pos := hc
  hbar_pos := a.hbar_pos

/-- The rationalized rest-energy-subtracted scalar dispersion. -/
def kgNRDispersion (a : Parameters) (c : ℝ) (p : Momentum) : ℝ :=
  momentumSq p / (Real.sqrt (a.mass ^ 2 + momentumSq p / c ^ 2) + a.mass)

def kgNRKineticEnergy (a : Parameters) (p : Momentum) : ℝ :=
  momentumSq p / (2 * a.mass)

theorem kg_nr_dispersion_denominator_pos (a : Parameters) (c : ℝ) (p : Momentum) :
    0 < Real.sqrt (a.mass ^ 2 + momentumSq p / c ^ 2) + a.mass :=
  add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) a.mass_pos

theorem kg_nr_energy_rescaling (a : Parameters) (c : ℝ) (hc : 0 < c) (p : Momentum) :
    energy (kgNRParameters a c hc) p =
      c ^ 2 * Real.sqrt (a.mass ^ 2 + momentumSq p / c ^ 2) := by
  have hc0 : c ≠ 0 := hc.ne'
  have hr : 0 ≤ a.mass ^ 2 + momentumSq p / c ^ 2 := by
    exact add_nonneg (sq_nonneg _) (div_nonneg (momentumSq_nonneg p) (sq_nonneg _))
  have hs := Real.sq_sqrt hr
  have he := energy_sq (kgNRParameters a c hc) p
  change energy (kgNRParameters a c hc) p ^ 2 =
    a.mass ^ 2 * c ^ 4 + c ^ 2 * momentumSq p at he
  have hs' : (c ^ 2 * Real.sqrt (a.mass ^ 2 + momentumSq p / c ^ 2)) ^ 2 =
      a.mass ^ 2 * c ^ 4 + c ^ 2 * momentumSq p := by
    rw [mul_pow, hs]
    field_simp
  have hn := mul_nonneg (sq_nonneg c) (Real.sqrt_nonneg (a.mass ^ 2 + momentumSq p / c ^ 2))
  nlinarith [energy_pos (kgNRParameters a c hc) p]

/-- Exact rationalization of the SAME original KG mass-shell energy. -/
theorem kg_nr_dispersion_is_rest_subtracted_energy
    (a : Parameters) (c : ℝ) (hc : 0 < c) (p : Momentum) :
    energy (kgNRParameters a c hc) p - a.mass * c ^ 2 = kgNRDispersion a c p := by
  rw [kg_nr_energy_rescaling]
  unfold kgNRDispersion
  apply (eq_div_iff (kg_nr_dispersion_denominator_pos a c p).ne').mpr
  have hr : 0 ≤ a.mass ^ 2 + momentumSq p / c ^ 2 :=
    add_nonneg (sq_nonneg _) (div_nonneg (momentumSq_nonneg p) (sq_nonneg _))
  have hs := Real.sq_sqrt hr
  have hcancel : c ^ 2 * (momentumSq p / c ^ 2) = momentumSq p := by
    field_simp
  nlinarith

/-- Pointwise dispersion convergence as the admitted speed goes to infinity.
There is no lattice, cutoff, or spatial mesh in this limit. -/
theorem kg_nr_dispersion_tendsto (a : Parameters) (p : Momentum) :
    Tendsto (fun c : ℝ => kgNRDispersion a c p) atTop
      (nhds (kgNRKineticEnergy a p)) := by
  have hinv : Tendsto (fun c : ℝ => (c⁻¹) ^ 2) atTop (nhds (0 : ℝ)) := by
    simpa using ((tendsto_inv_atTop_zero :
      Tendsto (fun c : ℝ => c⁻¹) atTop (nhds (0 : ℝ))).pow 2)
  have hratio : Tendsto (fun c : ℝ => momentumSq p / c ^ 2) atTop (nhds (0 : ℝ)) := by
    simpa [div_pow, div_eq_mul_inv] using hinv.const_mul (momentumSq p)
  have hs : Tendsto (fun c : ℝ => Real.sqrt (a.mass ^ 2 + momentumSq p / c ^ 2))
      atTop (nhds a.mass) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp
      (hratio.const_add (a.mass ^ 2))
    simpa [Real.sqrt_sq a.mass_pos.le] using h
  have hd : Tendsto (fun c : ℝ => Real.sqrt (a.mass ^ 2 + momentumSq p / c ^ 2) + a.mass)
      atTop (nhds (2 * a.mass)) := by
    simpa only [two_mul] using hs.add_const a.mass
  exact tendsto_const_nhds.div hd (mul_ne_zero (by norm_num) a.mass_pos.ne')

/-- The changing-speed branch remains the retained isolated one-particle
mass-shell branch, not an arbitrary Hilbert-space identification. -/
theorem kg_nr_branch_is_original_isolated_shell
    (a : Parameters) (c : ℝ) (hc : 0 < c) (n : ℕ) (x : ParticleConfiguration n) :
    particleFourMomentum (kgNRParameters a c hc) n x ∈
      wickOneMassShell (kgNRParameters a c hc) ↔ n = 1 :=
  wick_particle_in_one_mass_shell_iff (kgNRParameters a c hc) n x

end AASCKleinGordon
