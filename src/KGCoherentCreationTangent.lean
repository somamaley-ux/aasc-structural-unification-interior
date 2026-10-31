import KGWeylStrongDomain
import KGL2ProductMultilinear

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

def fockSectorEvaluationCLM (a : Parameters) (n : ℕ) :
    FockHilbert a →L[ℂ] bosonicHilbertSector a n :=
  ({ toFun:=fun v => v n
     map_add':=by intros; rfl
     map_smul':=by intros; rfl } : FockHilbert a →ₗ[ℂ] bosonicHilbertSector a n).mkContinuous 1
    (fun v => by simpa only [one_mul] using lp.norm_apply_le_norm (by norm_num : (2 : ENNReal)≠0) v n)

@[simp] theorem fockSectorEvaluationCLM_apply (a : Parameters) (n : ℕ) (v : FockHilbert a) :
    fockSectorEvaluationCLM a n v=v n := rfl

def coherentWeylVelocity (a : Parameters) (g f : 𝓢(Momentum,ℂ)) : FockHilbert a :=
  (Real.exp (‖oneParticleSchwartzToHilbert a f‖^2/2) : ℂ) •
    weylOperator a f (coherentVacuumTangent a g+weylCoherentPhaseSlope a g f • fockVacuum a)

def coherentCreationTangent (a : Parameters) (g f : 𝓢(Momentum,ℂ)) : FockHilbert a :=
  coherentWeylVelocity a g f+
    inner ℂ (oneParticleSchwartzToHilbert a g) (oneParticleSchwartzToHilbert a f) • exponentialVector a f

theorem exponentialVector_shift_weyl_formula (a : Parameters) (g f : 𝓢(Momentum,ℂ)) (t : ℝ) :
    exponentialVector a (f+(t : ℂ) • g)=
      Complex.exp (((t^2*‖oneParticleSchwartzToHilbert a g‖^2/2 : ℝ) : ℂ)+
        (t : ℂ)*inner ℂ (oneParticleSchwartzToHilbert a g) (oneParticleSchwartzToHilbert a f)) •
          weylRealLine a g t (exponentialVector a f) := by
  change _=Complex.exp _ • weylOperator a ((t : ℂ) • g) (exponentialVector a f)
  rw [weylOperator_exponentialVector,weylCoherentImage,smul_smul,← Complex.exp_add]
  have he : (((t^2*‖oneParticleSchwartzToHilbert a g‖^2/2 : ℝ) : ℂ)+
        (t : ℂ)*inner ℂ (oneParticleSchwartzToHilbert a g) (oneParticleSchwartzToHilbert a f))+
      (-((‖oneParticleSchwartzToHilbert a ((t : ℂ) • g)‖^2/2 : ℝ) : ℂ)-
        inner ℂ (oneParticleSchwartzToHilbert a ((t : ℂ) • g)) (oneParticleSchwartzToHilbert a f))=0 := by
    simp only [map_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,
      inner_smul_left,Complex.conj_ofReal]
    push_cast
    ring
  rw [he,Complex.exp_zero,one_smul]

theorem exponentialVector_shift_hasDerivAt_zero (a : Parameters) (g f : 𝓢(Momentum,ℂ)) :
    HasDerivAt (fun t : ℝ => exponentialVector a (f+(t : ℂ) • g))
      (coherentCreationTangent a g f) 0 := by
  let α:=inner ℂ (oneParticleSchwartzToHilbert a g) (oneParticleSchwartzToHilbert a f)
  have hr : HasDerivAt (fun t : ℝ => t^2*‖oneParticleSchwartzToHilbert a g‖^2/2) 0 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const
      (‖oneParticleSchwartzToHilbert a g‖^2)).div_const 2 using 1 <;> norm_num
  have hc : HasDerivAt (fun t : ℝ => ((t^2*‖oneParticleSchwartzToHilbert a g‖^2/2 : ℝ) : ℂ)) 0 0 := by
    convert Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hr using 1 <;> simp
  have ht : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    convert Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_id 0) using 1 <;> simp
  have hs:=(hc.add (ht.mul_const α)).cexp
  have hw:=weylRealLine_exponentialVector_hasDerivAt_zero a g f
  have hh:=hs.smul hw
  change HasDerivAt (fun t : ℝ => Complex.exp (((t^2*‖oneParticleSchwartzToHilbert a g‖^2/2 : ℝ) : ℂ)+
    (t : ℂ)*α) • weylRealLine a g t (exponentialVector a f)) _ 0 at hh
  simpa only [← exponentialVector_shift_weyl_formula,zero_pow (by norm_num : (2 : ℕ)≠0),
    Pi.add_apply,zero_mul,zero_div,Complex.ofReal_zero,zero_add,add_zero,one_mul,Complex.exp_zero,
    one_smul,weylRealLine_zero,coherentCreationTangent,coherentWeylVelocity,α] using hh

end AASCKleinGordon
