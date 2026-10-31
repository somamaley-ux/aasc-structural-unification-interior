import KGExponentialVacuumDerivative
import KGRealFieldWeylGroup

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem coherentVacuumTangent_eq_original_creation (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    coherentVacuumTangent a g=finiteParticleCoreToFock a (creationCore g vacuumCore) := by
  rw [vacuumCore,creationCore_lof,finiteParticleCoreToFock_on_sector]
  unfold coherentVacuumTangent
  congr 1
  simp only [coherentSector,Nat.factorial_one,Nat.cast_one,Real.sqrt_one,
    Complex.ofReal_one,inv_one,one_smul,bosonicTensorPowerHilbert]
  congr 1
  apply Subtype.ext
  ext x
  have hx : x=Fin.cons (x 0) Fin.elim0 := by
    funext i
    fin_cases i
    rfl
  rw [hx]
  change schwartzTensorPower g 1 (Fin.cons (x 0) Fin.elim0)=_
  rw [schwartzTensorPower_apply,creationSector_vacuum_apply]
  simp

theorem weylRealLine_vacuum_formula (a : Parameters) (g : 𝓢(Momentum,ℂ)) (t : ℝ) :
    weylRealLine a g t (fockVacuum a)=
      (Real.exp (-t^2*‖oneParticleSchwartzToHilbert a g‖^2/2) : ℂ) •
        exponentialVector a ((t : ℂ) • g) := by
  change weylOperator a ((t : ℂ) • g) (fockVacuum a)=_
  rw [weylOperator_vacuum,normalizedCoherentVector]
  congr 2
  rw [map_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

/-- Strong orbit derivative at the original vacuum, with the original norm and signs. -/
theorem weylRealLine_vacuum_hasDerivAt_zero (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    HasDerivAt (fun t : ℝ => weylRealLine a g t (fockVacuum a))
      (coherentVacuumTangent a g) 0 := by
  have hr : HasDerivAt (fun t : ℝ => Real.exp (-t^2*‖oneParticleSchwartzToHilbert a g‖^2/2)) 0 0 := by
    convert (((((hasDerivAt_id (0 : ℝ)).pow 2).neg.mul_const
      (‖oneParticleSchwartzToHilbert a g‖^2)).div_const 2).exp) using 1 <;> norm_num
  have hc : HasDerivAt (fun t : ℝ => (Real.exp (-t^2*‖oneParticleSchwartzToHilbert a g‖^2/2) : ℂ)) 0 0 := by
    convert Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hr using 1 <;> simp
  have hh:=hc.smul (exponentialVector_real_line_hasDerivAt_zero a g)
  simp only [zero_smul,zero_pow (by norm_num : (2 : ℕ)≠0),neg_zero,zero_mul,zero_div,
    Real.exp_zero,Complex.ofReal_one,one_smul,add_zero] at hh
  simpa only [weylRealLine_vacuum_formula] using hh

/-- Exact attachment to the ORIGINAL real smeared field at the original vacuum.
This is not yet an all-core derivative or a self-adjoint closure equality. -/
theorem original_real_field_vacuum_weyl_derivative (a : Parameters) (s : ℝ)
    (h : realSpacetimeTestSpace) :
    HasDerivAt (fun t : ℝ => realFieldWeylGroup a s h t (fockVacuum a))
      (Complex.I • finiteParticleCoreToFock a (spacetimeFieldCore a s h.val vacuumCore)) 0 := by
  have hh:=weylRealLine_vacuum_hasDerivAt_zero a (realFieldWeylLabelCLM a s h)
  rw [coherentVacuumTangent_eq_original_creation] at hh
  have hb:=congrArg (fun T : FiniteParticleCore →ₗ[ℂ] FiniteParticleCore =>
      finiteParticleCoreToFock a (T vacuumCore))
    (imaginary_creation_annihilation_difference a s h)
  simp only [LinearMap.sub_apply,annihilationCore_vacuum_zero,sub_zero,
    LinearMap.smul_apply,map_smul] at hb
  rw [hb] at hh
  exact hh

end AASCKleinGordon
