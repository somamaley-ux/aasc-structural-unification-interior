import KGWeylVacuumDerivative

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

def weylCoherentPhaseSlope (a : Parameters) (g f : 𝓢(Momentum,ℂ)) : ℂ :=
  inner ℂ (oneParticleSchwartzToHilbert a f) (oneParticleSchwartzToHilbert a g)-
    inner ℂ (oneParticleSchwartzToHilbert a g) (oneParticleSchwartzToHilbert a f)

theorem weylRealLine_exponentialVector_rebase (a : Parameters) (g f : 𝓢(Momentum,ℂ)) (t : ℝ) :
    weylRealLine a g t (exponentialVector a f)=
      Complex.exp (((‖oneParticleSchwartzToHilbert a f‖^2/2 : ℝ) : ℂ)+
        (t : ℂ)*weylCoherentPhaseSlope a g f) •
          weylOperator a f (weylRealLine a g t (fockVacuum a)) := by
  rw [weylRealLine_vacuum_formula,map_smul,weylOperator_exponentialVector]
  change weylOperator a ((t : ℂ) • g) (exponentialVector a f)=_
  rw [weylOperator_exponentialVector]
  simp only [weylCoherentImage,smul_smul]
  rw [add_comm f ((t : ℂ) • g)]
  congr 1
  simp only [Complex.ofReal_exp]
  rw [← Complex.exp_add,← Complex.exp_add]
  unfold weylCoherentPhaseSlope
  simp only [map_smul,inner_smul_left,inner_smul_right,Complex.conj_ofReal,
    norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  push_cast
  ring

/-- A dense coherent-family strong derivative, derived from the actual vacuum
norm derivative and the actual Weyl relations. No generator premise is received. -/
theorem weylRealLine_exponentialVector_hasDerivAt_zero
    (a : Parameters) (g f : 𝓢(Momentum,ℂ)) :
    HasDerivAt (fun t : ℝ => weylRealLine a g t (exponentialVector a f))
      ((Real.exp (‖oneParticleSchwartzToHilbert a f‖^2/2) : ℂ) •
        weylOperator a f (coherentVacuumTangent a g+
          weylCoherentPhaseSlope a g f • fockVacuum a)) 0 := by
  let A:=weylCoherentPhaseSlope a g f
  let n:ℂ:=((‖oneParticleSchwartzToHilbert a f‖^2/2 : ℝ) : ℂ)
  have ht : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    convert Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_id 0) using 1 <;> simp
  have hs := ((ht.mul_const A).const_add n).cexp
  have hv := ((weylOperator a f).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (weylRealLine_vacuum_hasDerivAt_zero a g)
  have hh:=hs.smul hv
  simp only [Complex.ofReal_zero,zero_mul,add_zero,one_mul] at hh
  change HasDerivAt (fun t : ℝ => Complex.exp (n+(t : ℂ)*A) •
      weylOperator a f (weylRealLine a g t (fockVacuum a)))
    (Complex.exp n • weylOperator a f (coherentVacuumTangent a g)+
      (Complex.exp n*A) • weylOperator a f (weylRealLine a g 0 (fockVacuum a))) 0 at hh
  rw [weylRealLine_zero] at hh
  have he : Complex.exp n • weylOperator a f (coherentVacuumTangent a g)+
      (Complex.exp n* A) • weylOperator a f (fockVacuum a)=
      (Real.exp (‖oneParticleSchwartzToHilbert a f‖^2/2) : ℂ) •
        weylOperator a f (coherentVacuumTangent a g+A • fockVacuum a) := by
    simp only [n,map_add,map_smul,smul_add,smul_smul,Complex.ofReal_exp]
  rw [he] at hh
  simpa only [weylRealLine_exponentialVector_rebase,A,n] using hh

end AASCKleinGordon
