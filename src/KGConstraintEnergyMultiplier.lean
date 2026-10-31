import KGConstraintEnergyFlow
import KGPhaseAERHamiltonian

/-! Actual original KG physical-time dynamics with the norm constraint added.
The multiplier is a phase frequency; its energy-baseline shift is hbar*lambda.
The representative unit slice is used only for the phase reduction, never as
the original qualification/standing gate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
local instance (a : Parameters) : (n : ℕ) → NormedSpace ℂ (bosonicHilbertSector a n) :=
  fun _ => inferInstance
local instance (a : Parameters) (n : ℕ) : NormedSpace ℝ (bosonicHilbertSector a n) :=
  NormedSpace.restrictScalars ℝ ℂ (bosonicHilbertSector a n)
local instance (a : Parameters) : NormedSpace ℝ (FockHilbert a) :=
  NormedSpace.restrictScalars ℝ ℂ (FockHilbert a)
local instance (a : Parameters) : NormedSpace ℝ (fockCoreDomain a) :=
  NormedSpace.restrictScalars ℝ ℂ (fockCoreDomain a)
attribute [local irreducible] kgConstraintEnergyOperator kgConstraintEnergyTime kgConstraintEnergyVector kgConstraintEnergyH0

def kgConstraintEnergyHamiltonian (a : Parameters) (lam : ℝ) (u : fockCoreDomain a) : ℝ :=
  kgConstraintEnergyH0 a u + lam * phaseAERConstraint u

def kgConstraintEnergyHamiltonianVector (a : Parameters) (lam : ℝ)
    (u : fockCoreDomain a) : fockCoreDomain a :=
  kgConstraintEnergyVector a u + lam • (-(Complex.I • u))

private theorem kg_constraint_energy_generic_calibration
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (h : ℝ) (w : E) :
    Translation.coefficient h • w = h⁻¹ • (-(Complex.I • w)) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), ← neg_smul, smul_smul]
  congr 1
  change (-Complex.I / (h : ℂ)) = ((h⁻¹ : ℝ) : ℂ) * (-Complex.I)
  push_cast
  ring

private theorem kg_constraint_energy_generic_pairing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (h : ℝ) (w v : E) :
    phaseAEROmega (Translation.coefficient h • w) v = h⁻¹ * (inner ℂ w v).re := by
  rw [kg_constraint_energy_generic_calibration, phaseAER_omega_smul_left,
    phaseAER_constraint_hamiltonian, phaseAER_constraint_differential_apply]

private theorem kg_constraint_energy_generic_multiplier_pairing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (x u v : E) (lam : ℝ) :
    phaseAEROmega (x + lam • (-(Complex.I • u))) v =
      phaseAEROmega x v + lam * phaseAERConstraintDifferential u v := by
  rw [phaseAER_omega_add_left, phaseAER_omega_smul_left, phaseAER_constraint_hamiltonian]

private theorem kg_constraint_energy_generic_vertical
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (x u : E) (lam : ℝ) :
    x + lam • (-(Complex.I • u)) - x ∈ phaseAERVertical u := by
  rw [add_sub_cancel_left]
  exact Submodule.smul_mem _ lam (Submodule.neg_mem _
    (Submodule.subset_span (Set.mem_singleton (Complex.I • u))))

private theorem kg_constraint_energy_generic_phase_vector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (lam : ℝ) (w x : E) :
    w + lam • (-(Complex.I • x)) = Translation.phase 1 0 lam • w +
      (Translation.coefficient 1 * (lam : ℂ)) • x := by
  rw [Translation.phase_zero, one_smul]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_neg, smul_smul]
  simp only [Translation.coefficient, Complex.ofReal_one, div_one]
  congr 1
  rw [← neg_smul]
  congr 1
  rw [neg_mul]
  exact congrArg Neg.neg (mul_comm (lam : ℂ) Complex.I)

private theorem kg_constraint_energy_quadratic_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (L : E →ₗ[ℂ] E) (α : ℝ) (c : ℂ) (u : E) :
    α * (inner ℂ (c • u) (L (c • u))).re =
      ‖c‖ ^ 2 * (α * (inner ℂ u (L u)).re) := by
  have hs : (starRingEnd ℂ) c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [L.map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, hs]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem kg_constraint_energy_h0_smul (a : Parameters) (c : ℂ) (u : fockCoreDomain a) :
    kgConstraintEnergyH0 a (c • u) = ‖c‖ ^ 2 * kgConstraintEnergyH0 a u := by
  unfold kgConstraintEnergyH0
  change (1 / (2 * a.hbar)) * (inner ℂ (c • u) (kgConstraintEnergyOperator a (c • u))).re =
    ‖c‖ ^ 2 * ((1 / (2 * a.hbar)) * (inner ℂ u (kgConstraintEnergyOperator a u)).re)
  exact kg_constraint_energy_quadratic_smul (kgConstraintEnergyOperator a) (1 / (2 * a.hbar)) c u

theorem kg_constraint_energy_h0_phase_invariant (a : Parameters) (c : ℂ)
    (hc : ‖c‖ = 1) (u : fockCoreDomain a) :
    kgConstraintEnergyH0 a (c • u) = kgConstraintEnergyH0 a u := by
  rw [kg_constraint_energy_h0_smul, hc]
  simp

theorem kg_constraint_energy_vector_calibration (a : Parameters) (u : fockCoreDomain a) :
    kgConstraintEnergyVector a u = a.hbar⁻¹ • (-(Complex.I • kgConstraintEnergyOperator a u)) := by
  unfold kgConstraintEnergyVector
  exact kg_constraint_energy_generic_calibration a.hbar (kgConstraintEnergyOperator a u)

theorem kg_constraint_energy_h0_hamiltonian (a : Parameters) (u v : fockCoreDomain a) :
    phaseAEROmega (kgConstraintEnergyVector a u) v =
      a.hbar⁻¹ * (inner ℂ (kgConstraintEnergyOperator a u) v).re := by
  unfold kgConstraintEnergyVector
  exact kg_constraint_energy_generic_pairing a.hbar (kgConstraintEnergyOperator a u) v

theorem kg_constraint_energy_hamiltonian_pairing (a : Parameters) (lam : ℝ)
    (u v : fockCoreDomain a) :
    phaseAEROmega (kgConstraintEnergyHamiltonianVector a lam u) v =
      a.hbar⁻¹ * (inner ℂ (kgConstraintEnergyOperator a u) v).re +
        lam * phaseAERConstraintDifferential u v := by
  change phaseAEROmega (kgConstraintEnergyVector a u + lam • (-(Complex.I • u))) v = _
  exact (kg_constraint_energy_generic_multiplier_pairing (kgConstraintEnergyVector a u) u v lam).trans
    (congrArg (fun r : ℝ => r + lam * phaseAERConstraintDifferential u v)
      (kg_constraint_energy_h0_hamiltonian a u v))

theorem kg_constraint_energy_hamiltonian_directional (a : Parameters) (lam : ℝ)
    (u v : fockCoreDomain a) :
    HasDerivAt (fun t : ℝ => kgConstraintEnergyHamiltonian a lam (u + (t : ℂ) • v))
      (phaseAEROmega (kgConstraintEnergyHamiltonianVector a lam u) v) 0 := by
  have hl : HasDerivAt (fun t : ℝ => u + (t : ℂ) • v) v 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt.smul_const v).const_add u
  have hp : HasDerivAt (fun t : ℝ => phaseAERConstraint (u + (t : ℂ) • v))
      (phaseAERConstraintDifferential u v) 0 := by
    have hf : HasFDerivAt phaseAERConstraint (phaseAERConstraintDifferential u)
        (u + ((0 : ℝ) : ℂ) • v) := by simpa using phaseAER_constraint_hasFDerivAt u
    exact hf.comp_hasDerivAt 0 hl
  rw [kg_constraint_energy_hamiltonian_pairing]
  exact (kg_constraint_energy_directional_derivative a u v).add (hp.const_mul lam)

theorem kg_constraint_energy_hamiltonian_unit (a : Parameters) (lam : ℝ)
    (u : fockCoreDomain a) (hu : ‖u‖ = 1) :
    kgConstraintEnergyHamiltonian a lam u = kgConstraintEnergyH0 a u := by
  rw [kgConstraintEnergyHamiltonian, (phaseAER_constraint_unit u).mpr hu]
  simp

theorem kg_constraint_energy_multiplier_vertical (a : Parameters) (lam : ℝ)
    (u : fockCoreDomain a) :
    kgConstraintEnergyHamiltonianVector a lam u - kgConstraintEnergyVector a u ∈ phaseAERVertical u := by
  change kgConstraintEnergyVector a u + lam • (-(Complex.I • u)) -
    kgConstraintEnergyVector a u ∈ phaseAERVertical u
  exact kg_constraint_energy_generic_vertical (kgConstraintEnergyVector a u) u lam

theorem kg_constraint_energy_same_reduced_vector (a : Parameters) (lam : ℝ)
    (u : fockCoreDomain a) (hu : ‖u‖ = 1) :
    phaseAERQ u (kgConstraintEnergyHamiltonianVector a lam u) =
      phaseAERQ u (kgConstraintEnergyVector a u) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (phaseAER_q_zero_iff_vertical u hu _).mpr
    (kg_constraint_energy_multiplier_vertical a lam u)

/-- Explicit phase TIMES the same original physical-time evolution. -/
def kgConstraintEnergyMultiplierFlow (a : Parameters) (lam t : ℝ)
    (u : fockCoreDomain a) : fockCoreDomain a :=
  Translation.phase 1 t lam • kgConstraintEnergyTime a t u

theorem kg_constraint_energy_multiplier_phase_nonzero (lam t : ℝ) :
    Translation.phase 1 t lam ≠ 0 := Complex.exp_ne_zero _

theorem kg_constraint_energy_multiplier_flow_original (a : Parameters) (lam t : ℝ)
    (u : fockCoreDomain a) :
    kgConstraintEnergyMultiplierFlow a lam t u = Translation.phase 1 t lam •
      kgCorePoincareIsometry a ⟨Multiplicative.ofAdd (timeTranslationEvent a t), 1⟩ u := by
  exact congrArg (fun v : fockCoreDomain a => Translation.phase 1 t lam • v)
    (kg_constraint_energy_time_original a t u)

theorem kg_constraint_energy_multiplier_flow_zero (a : Parameters) (lam : ℝ)
    (u : fockCoreDomain a) : kgConstraintEnergyMultiplierFlow a lam 0 u = u := by
  simp [kgConstraintEnergyMultiplierFlow, kg_constraint_energy_time_zero]

theorem kg_constraint_energy_multiplier_flow_norm (a : Parameters) (lam t : ℝ)
    (u : fockCoreDomain a) : ‖kgConstraintEnergyMultiplierFlow a lam t u‖ = ‖u‖ := by
  simp [kgConstraintEnergyMultiplierFlow, norm_smul]

theorem kg_constraint_energy_multiplier_flow_add (a : Parameters) (lam t s : ℝ)
    (u : fockCoreDomain a) :
    kgConstraintEnergyMultiplierFlow a lam (t + s) u =
      kgConstraintEnergyMultiplierFlow a lam t (kgConstraintEnergyMultiplierFlow a lam s u) := by
  simp only [kgConstraintEnergyMultiplierFlow, Translation.phase_add,
    kg_constraint_energy_time_add, map_smul, smul_smul]

theorem kg_constraint_energy_multiplier_flow_constraint (a : Parameters) (lam t : ℝ)
    (u : fockCoreDomain a) :
    phaseAERConstraint (kgConstraintEnergyMultiplierFlow a lam t u) = phaseAERConstraint u := by
  simp only [phaseAERConstraint, kg_constraint_energy_multiplier_flow_norm]

theorem kg_constraint_energy_multiplier_flow_derivative (a : Parameters) (lam : ℝ)
    (u : fockCoreDomain a) :
    HasDerivAt (fun t : ℝ => (kgConstraintEnergyMultiplierFlow a lam t u).val)
      (kgConstraintEnergyHamiltonianVector a lam u).val 0 := by
  have hp := Translation.phase_hasDerivAt_zero 1 lam
  have hu := kg_constraint_energy_time_derivative a u
  have h := hp.smul hu
  convert h using 1
  · change (kgConstraintEnergyVector a u).val +
      (lam • (-(Complex.I • u))).val =
        Translation.phase 1 0 lam • (kgConstraintEnergyVector a u).val +
          (Translation.coefficient 1 * (lam : ℂ)) • (kgConstraintEnergyTime a 0 u).val
    have hz : (kgConstraintEnergyTime a 0 u).val = u.val :=
      congrArg Subtype.val (kg_constraint_energy_time_zero a u)
    rw [hz]
    change (kgConstraintEnergyVector a u).val + lam • (-(Complex.I • u.val)) = _
    exact kg_constraint_energy_generic_phase_vector lam (kgConstraintEnergyVector a u).val u.val

theorem kg_constraint_energy_multiplier_flow_derivative_at (a : Parameters) (lam t : ℝ)
    (u : fockCoreDomain a) :
    HasDerivAt (fun r : ℝ => (kgConstraintEnergyMultiplierFlow a lam r u).val)
      (kgConstraintEnergyHamiltonianVector a lam (kgConstraintEnergyMultiplierFlow a lam t u)).val t := by
  let w := kgConstraintEnergyMultiplierFlow a lam t u
  have hz : HasDerivAt (fun r : ℝ => (kgConstraintEnergyMultiplierFlow a lam r w).val)
      (kgConstraintEnergyHamiltonianVector a lam w).val (t - t) := by
    simpa using kg_constraint_energy_multiplier_flow_derivative a lam w
  have h := hz.scomp t (h := fun r : ℝ => r - t) ((hasDerivAt_id t).sub_const t)
  dsimp only [w] at h
  have he (r : ℝ) : kgConstraintEnergyMultiplierFlow a lam (r - t)
      (kgConstraintEnergyMultiplierFlow a lam t u) = kgConstraintEnergyMultiplierFlow a lam r u := by
    rw [← kg_constraint_energy_multiplier_flow_add, sub_add_cancel]
  simpa only [Function.comp_def, one_smul, he] using h

theorem kg_constraint_energy_hamiltonian_tangent (a : Parameters) (lam : ℝ)
    (u : fockCoreDomain a) :
    kgConstraintEnergyHamiltonianVector a lam u ∈ phaseAERTangent u := by
  have hf : HasFDerivAt phaseAERConstraint (phaseAERConstraintDifferential u.val)
      (kgConstraintEnergyMultiplierFlow a lam 0 u).val := by
    rw [kg_constraint_energy_multiplier_flow_zero]
    exact phaseAER_constraint_hasFDerivAt u.val
  have hd := hf.comp_hasDerivAt 0 (kg_constraint_energy_multiplier_flow_derivative a lam u)
  have he : (fun t : ℝ => phaseAERConstraint (kgConstraintEnergyMultiplierFlow a lam t u).val) =
      (fun _ : ℝ => phaseAERConstraint u.val) := by
    funext t
    exact kg_constraint_energy_multiplier_flow_constraint a lam t u
  change HasDerivAt (fun t : ℝ => phaseAERConstraint (kgConstraintEnergyMultiplierFlow a lam t u).val) _ 0 at hd
  rw [he] at hd
  exact hd.unique (hasDerivAt_const 0 (phaseAERConstraint u.val))

end AASCKleinGordon
