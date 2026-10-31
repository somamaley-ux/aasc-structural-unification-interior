import KGPhaseAERGeometry

/-! Continuous Hamiltonians for the representative norm constraint. The Riesz
claim below concerns the continuous real dual of a complete Hilbert carrier;
it says nothing about arbitrary algebraic covectors or unbounded source forms. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace AASCKleinGordon
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
local instance : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E

def phaseAERConstraint (v : E) : ℝ := (‖v‖^2-1)/2

def phaseAERConstraintDifferential (u : E) : E →L[ℝ] ℝ := phaseAERInnerReCLM u

@[simp] theorem phaseAER_constraint_differential_apply (u v : E) :
    phaseAERConstraintDifferential u v = (inner ℂ u v).re := rfl

theorem phaseAER_constraint_hasFDerivAt (u : E) :
    HasFDerivAt phaseAERConstraint (phaseAERConstraintDifferential u) u := by
  have h := ((hasStrictFDerivAt_norm_sq u).hasFDerivAt.sub_const 1).const_smul (1/2 : ℝ)
  convert h using 1
  · funext v
    simp [phaseAERConstraint,div_eq_mul_inv,mul_comm]
  · ext v
    simp [phaseAERConstraintDifferential,phaseAERInnerReCLM]
    rfl


theorem phaseAER_constraint_differential_self (u : E) (hu : ‖u‖=1) :
    phaseAERConstraintDifferential u u=1 := by
  change (inner ℂ u u).re=1
  have h := (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
  simpa only [hu,one_pow] using h

theorem phaseAER_constraint_differential_ne_zero (u : E) (hu : ‖u‖=1) :
    phaseAERConstraintDifferential u≠0 := by
  intro h
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L u) h
  change phaseAERConstraintDifferential u u=0 at hh
  rw [phaseAER_constraint_differential_self u hu] at hh
  norm_num at hh

theorem phaseAER_constraint_differential_surjective (u : E) (hu : ‖u‖=1) :
    Function.Surjective (phaseAERConstraintDifferential u) := by
  intro r
  refine ⟨r • u,?_⟩
  rw [map_smul,phaseAER_constraint_differential_self u hu]
  simp

omit [InnerProductSpace ℂ E] in
theorem phaseAER_constraint_unit (u : E) :
    phaseAERConstraint u = 0 ↔ ‖u‖=1 := by
  simp only [phaseAERConstraint,div_eq_zero_iff,sub_eq_zero,OfNat.ofNat_ne_zero,or_false]
  constructor
  · intro h
    nlinarith [norm_nonneg u]
  · intro h
    rw [h]
    norm_num

theorem phaseAER_constraint_tangent (u v : E) :
    phaseAERConstraintDifferential u v = 0 ↔ v ∈ phaseAERTangent u := Iff.rfl

theorem phaseAER_constraint_hamiltonian (u v : E) :
    phaseAEROmega (-(Complex.I • u)) v = phaseAERConstraintDifferential u v := by
  simp [phaseAEROmega,inner_neg_left,inner_smul_left,Complex.mul_im]

def phaseAERPhaseFlow (t : ℝ) (u : E) : E :=
  Complex.exp (-(t : ℂ)*Complex.I) • u

theorem phaseAER_phase_flow_zero (u : E) : phaseAERPhaseFlow 0 u = u := by
  simp [phaseAERPhaseFlow]

theorem phaseAER_phase_flow_norm (t : ℝ) (u : E) : ‖phaseAERPhaseFlow t u‖=‖u‖ := by
  simp [phaseAERPhaseFlow,norm_smul,Complex.norm_exp,Complex.mul_re]

theorem phaseAER_phase_flow_constraint (t : ℝ) (u : E) :
    phaseAERConstraint (phaseAERPhaseFlow t u)=phaseAERConstraint u := by
  rw [phaseAERConstraint,phaseAER_phase_flow_norm]
  rfl

theorem phaseAER_phase_flow_hasDerivAt (t : ℝ) (u : E) :
    HasDerivAt (fun r : ℝ => phaseAERPhaseFlow r u)
      (-(Complex.I • phaseAERPhaseFlow t u)) t := by
  have hc : HasDerivAt (fun r : ℝ => -(r : ℂ)*Complex.I) (-Complex.I) t := by
    simpa using (Complex.ofRealCLM.hasDerivAt.neg.mul_const Complex.I)
  have h := hc.cexp.smul_const u
  convert h using 1
  simp [phaseAERPhaseFlow,smul_smul,mul_comm]

theorem phaseAER_phase_flow_hamiltonian (t : ℝ) (u v : E) :
    phaseAEROmega (-(Complex.I • phaseAERPhaseFlow t u)) v =
      phaseAERConstraintDifferential (phaseAERPhaseFlow t u) v :=
  phaseAER_constraint_hamiltonian _ _

theorem phaseAER_continuous_dual_hamiltonian [CompleteSpace E] (ℓ : E →L[ℝ] ℝ) :
    ∃X : E,∀v : E,phaseAEROmega X v = ℓ v := by
  let a := (InnerProductSpace.toDual ℝ E).symm ℓ
  refine ⟨-(Complex.I • a),?_⟩
  intro v
  rw [phaseAER_constraint_hamiltonian]
  change (inner ℝ a v) = ℓ v
  exact InnerProductSpace.toDual_symm_apply

#print axioms phaseAER_constraint_differential_surjective
#print axioms phaseAER_constraint_hasFDerivAt
#print axioms phaseAER_phase_flow_hasDerivAt
#print axioms phaseAER_continuous_dual_hamiltonian
end AASCKleinGordon
