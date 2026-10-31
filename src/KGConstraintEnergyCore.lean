import KGFockExactGenerators

/-! The actual retained KG energy on its original invariant common core.
Only real affine-core directional differentiation is asserted; the unbounded
operator is not claimed bounded or globally differentiable in Hilbert norm. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace AASCKleinGordon

def kgConstraintEnergyOperator (a : Parameters) :
    fockCoreDomain a →ₗ[ℂ] fockCoreDomain a where
  toFun u := ⟨fockCoreEnergy a u, fockCoreEnergy_preserves_common_domain a u⟩
  map_add' u v := Subtype.ext ((fockCoreEnergy a).map_add u v)
  map_smul' c u := Subtype.ext ((fockCoreEnergy a).map_smul c u)

theorem kg_constraint_energy_operator_original (a : Parameters) (u : FiniteParticleCore) :
    (kgConstraintEnergyOperator a (includedFockCore a u)).val =
      finiteParticleCoreToFock a (coreEnergy a u) :=
  fockCoreEnergy_on_original_core a u

theorem kg_constraint_energy_operator_symmetric (a : Parameters) (u v : fockCoreDomain a) :
    inner ℂ u (kgConstraintEnergyOperator a v) =
      inner ℂ (kgConstraintEnergyOperator a u) v := by
  have hT := fockMaximalEnergy_selfAdjoint a
  have hformal : (fockMaximalEnergy a).IsFormalAdjoint (fockMaximalEnergy a) := by
    simpa only [LinearPMap.isSelfAdjoint_def.mp hT] using
      (LinearPMap.adjoint_isFormalAdjoint hT.dense_domain)
  have hu := LinearPMap.apply_comp_inclusion (fockCoreEnergy_le_maximal a) u
  have hv := LinearPMap.apply_comp_inclusion (fockCoreEnergy_le_maximal a) v
  have h := hformal (Submodule.inclusion (fockCoreEnergy_le_maximal a).1 u)
    (Submodule.inclusion (fockCoreEnergy_le_maximal a).1 v)
  change inner ℂ u.val (fockCoreEnergy a v) = inner ℂ (fockCoreEnergy a u) v.val
  rw [hu, hv]
  exact h.symm

/-- Original quadratic energy, with explicit physical action calibration for
the convention Omega = Im inner and actual physical-time evolution. -/
def kgConstraintEnergyH0 (a : Parameters) (u : fockCoreDomain a) : ℝ :=
  (1 / (2 * a.hbar)) * (inner ℂ u (kgConstraintEnergyOperator a u)).re

private theorem kg_constraint_energy_line_derivative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (L : E →ₗ[ℂ] E) (u v : E) (α : ℝ) :
    HasDerivAt (fun t : ℝ => α * (inner ℂ (u + (t : ℂ) • v)
      (L (u + (t : ℂ) • v))).re)
      (α * ((inner ℂ u (L v)).re + (inner ℂ v (L u)).re)) 0 := by
  simp_rw [L.map_add, L.map_smul]
  have ht : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have h1 : HasDerivAt (fun t : ℝ => u + (t : ℂ) • v) v 0 := by
    simpa using (ht.smul_const v).const_add u
  have h2 : HasDerivAt (fun t : ℝ => L u + (t : ℂ) • L v) (L v) 0 := by
    simpa using (ht.smul_const (L v)).const_add (L u)
  have hi := h1.inner ℂ h2
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hi
  simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_zero,
    zero_smul, add_zero, Complex.add_re] using hr.const_mul α

private theorem kg_constraint_energy_symmetric_line_derivative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (L : E →ₗ[ℂ] E)
    (hL : ∀ u v : E, inner ℂ u (L v) = inner ℂ (L u) v)
    (hbar : ℝ) (u v : E) :
    HasDerivAt (fun t : ℝ => (1 / (2 * hbar)) *
      (inner ℂ (u + (t : ℂ) • v) (L (u + (t : ℂ) • v))).re)
      (hbar⁻¹ * (inner ℂ (L u) v).re) 0 := by
  have h := kg_constraint_energy_line_derivative L u v (1 / (2 * hbar))
  have hs : (1 / (2 * hbar)) * ((inner ℂ u (L v)).re + (inner ℂ v (L u)).re) =
      hbar⁻¹ * (inner ℂ (L u) v).re := by
    have hr : (inner ℂ v (L u)).re = (inner ℂ (L u) v).re := by
      simpa only [Complex.conj_re] using congrArg Complex.re (inner_conj_symm (L u) v)
    rw [congrArg Complex.re (hL u v), hr]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hs] at h
  exact h

attribute [local irreducible] kgConstraintEnergyOperator

/-- Directional derivative on every original core affine line, proved by
explicit affine input and output curves rather than global continuity of E. -/
theorem kg_constraint_energy_directional_derivative (a : Parameters)
    (u v : fockCoreDomain a) :
    HasDerivAt (fun t : ℝ => kgConstraintEnergyH0 a (u + (t : ℂ) • v))
      (a.hbar⁻¹ * (inner ℂ (kgConstraintEnergyOperator a u) v).re) 0 := by
  change HasDerivAt (fun t : ℝ => (1 / (2 * a.hbar)) *
    (inner ℂ (u + (t : ℂ) • v) (kgConstraintEnergyOperator a (u + (t : ℂ) • v))).re)
      (a.hbar⁻¹ * (inner ℂ (kgConstraintEnergyOperator a u) v).re) 0
  exact @kg_constraint_energy_symmetric_line_derivative (fockCoreDomain a)
    (inferInstance : NormedAddCommGroup (fockCoreDomain a))
    (inferInstance : InnerProductSpace ℂ (fockCoreDomain a)) (kgConstraintEnergyOperator a)
      (kg_constraint_energy_operator_symmetric a) a.hbar u v

end AASCKleinGordon
