import KGCoherentContinuity
import GaussianStrongDerivative

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

/-- The actual original one-particle sector embedded in the original Fock sum. -/
def coherentVacuumTangent (a : Parameters) (g : 𝓢(Momentum,ℂ)) : FockHilbert a :=
  lp.single (E:=fun n => bosonicHilbertSector a n) 2 1 (coherentSector a g 1)

theorem coherentVacuumTangent_norm_sq (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    ‖coherentVacuumTangent a g‖^2=‖oneParticleSchwartzToHilbert a g‖^2 := by
  rw [coherentVacuumTangent,lp.norm_single (by norm_num : (0 : ENNReal)<2),coherentSector_norm_sq]
  norm_num

theorem coherentVacuumTangent_inner (a : Parameters) (g f : 𝓢(Momentum,ℂ)) :
    inner ℂ (coherentVacuumTangent a g) (exponentialVector a f)=
      inner ℂ (oneParticleSchwartzToHilbert a g) (oneParticleSchwartzToHilbert a f) := by
  rw [coherentVacuumTangent,lp.inner_single_left,exponentialVector_component,coherentSector_inner]
  norm_num

theorem inner_coherentVacuumTangent (a : Parameters) (g f : 𝓢(Momentum,ℂ)) :
    inner ℂ (exponentialVector a f) (coherentVacuumTangent a g)=
      inner ℂ (oneParticleSchwartzToHilbert a f) (oneParticleSchwartzToHilbert a g) := by
  rw [← inner_conj_symm,coherentVacuumTangent_inner,inner_conj_symm]

theorem exponentialVector_real_line_remainder (a : Parameters) (g : 𝓢(Momentum,ℂ)) (t : ℝ) :
    ‖exponentialVector a ((t : ℂ) • g)-exponentialVector a 0-
        t • coherentVacuumTangent a g‖^2=
      Real.exp (t^2*‖oneParticleSchwartzToHilbert a g‖^2)-1-
        t^2*‖oneParticleSchwartzToHilbert a g‖^2 := by
  rw [norm_sub_sq (𝕜:=ℂ),norm_sub_sq (𝕜:=ℂ),norm_smul,
    exponentialVector_norm_sq,exponentialVector_norm_sq,
    exponentialVector_inner,inner_sub_left]
  simp only [inner_smul_right_eq_smul,inner_coherentVacuumTangent,
    mul_pow,coherentVacuumTangent_norm_sq]
  simp only [map_zero,inner_zero_right,inner_zero_left,Complex.exp_zero,
    RCLike.one_re,norm_zero,zero_pow (by norm_num : (2 : ℕ)≠0),Real.exp_zero,
    map_smul,inner_smul_left,Complex.conj_ofReal,inner_self_eq_norm_sq_to_K,
    norm_smul,Complex.norm_real,Real.norm_eq_abs,
    mul_pow,sq_abs]
  simp only [smul_zero,sub_zero,RCLike.smul_re,pow_two,RCLike.mul_re,
    RCLike.mul_im,RCLike.ofReal_re,RCLike.ofReal_im,mul_zero,zero_mul,sub_zero,
    zero_add]
  change Real.exp (t*t*(‖oneParticleSchwartzToHilbert a g‖*‖oneParticleSchwartzToHilbert a g‖))-2*1+1-
      2*(t*(t*(‖oneParticleSchwartzToHilbert a g‖*‖oneParticleSchwartzToHilbert a g‖)))+
      t*t*(‖oneParticleSchwartzToHilbert a g‖*‖oneParticleSchwartzToHilbert a g‖)=_
  ring

/-- Actual strong derivative in the original Hilbert norm. -/
theorem exponentialVector_real_line_hasDerivAt_zero (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    HasDerivAt (fun t : ℝ => exponentialVector a ((t : ℂ) • g))
      (coherentVacuumTangent a g) 0 := by
  apply hasDerivAt_of_gaussian_remainder _ _ (‖oneParticleSchwartzToHilbert a g‖^2)
  intro t
  simpa only [Complex.ofReal_zero,zero_smul] using exponentialVector_real_line_remainder a g t

end AASCKleinGordon
