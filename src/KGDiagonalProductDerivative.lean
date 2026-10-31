import KGL2ProductMultilinear
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Pi

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem particleL2Product_diagonal_hasDerivAt (a : Parameters) (f g : 𝓢(Momentum,ℂ)) (n : ℕ) :
    HasDerivAt (fun t : ℝ => particleL2Product a n
        (fun _ => oneParticleSchwartzToHilbert a (f+(t : ℂ) • g)))
      (∑ i : Fin n,particleL2Product a n
        (Function.update (fun _ => oneParticleSchwartzToHilbert a f) i (oneParticleSchwartzToHilbert a g))) 0 := by
  classical
  have ht : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    convert Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_id 0) using 1 <;> simp
  have hj : HasDerivAt (fun t : ℝ => oneParticleSchwartzToHilbert a f+
      (t : ℂ) • oneParticleSchwartzToHilbert a g) (oneParticleSchwartzToHilbert a g) 0 := by
    simpa only [one_smul] using (ht.smul_const (oneParticleSchwartzToHilbert a g)).const_add
      (oneParticleSchwartzToHilbert a f)
  have hp : HasDerivAt (fun t : ℝ => fun _ : Fin n => oneParticleSchwartzToHilbert a f+
      (t : ℂ) • oneParticleSchwartzToHilbert a g) (fun _ : Fin n => oneParticleSchwartzToHilbert a g) 0 :=
    hasDerivAt_pi.mpr (fun _ => hj)
  have hm:=((particleL2ProductCMLM a n).hasFDerivAt (fun _ => oneParticleSchwartzToHilbert a f+
    ((0 : ℝ) : ℂ) • oneParticleSchwartzToHilbert a g)).restrictScalars ℝ
  have hh:=hm.comp_hasDerivAt 0 hp
  simpa only [map_add,map_smul,Complex.ofReal_zero,zero_smul,add_zero,
    Function.comp_def,ContinuousLinearMap.coe_restrictScalars',
    ContinuousMultilinearMap.linearDeriv_apply,particleL2ProductCMLM_apply] using hh

end AASCKleinGordon
