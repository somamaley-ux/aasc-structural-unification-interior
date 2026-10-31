import KGCoherentContinuity

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

/-- The concrete Weyl displacement prescription on actual exponential vectors.
Extension to a full bounded operator requires its proved linear-span descent and totality. -/
def weylCoherentImage (a : Parameters) (g f : 𝓢(Momentum,ℂ)) : FockHilbert a :=
  Complex.exp (-((‖oneParticleSchwartzToHilbert a g‖^2/2 : ℝ) : ℂ)-
    inner ℂ (oneParticleSchwartzToHilbert a g) (oneParticleSchwartzToHilbert a f)) •
      exponentialVector a (f+g)

theorem weylCoherentImage_inner (a : Parameters) (g f h : 𝓢(Momentum,ℂ)) :
    inner ℂ (weylCoherentImage a g f) (weylCoherentImage a g h)=
      inner ℂ (exponentialVector a f) (exponentialVector a h) := by
  rw [weylCoherentImage,weylCoherentImage,inner_smul_left,inner_smul_right,
    exponentialVector_inner,exponentialVector_inner]
  rw [starRingEnd_apply,Complex.star_def,← Complex.exp_conj]
  simp only [map_add,inner_add_left,inner_add_right,map_sub,map_neg,Complex.conj_ofReal,inner_conj_symm,
    inner_self_eq_norm_sq_to_K]
  rw [← Complex.exp_add,← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  change -((‖oneParticleSchwartzToHilbert a g‖ : ℂ)^2)+
      inner ℂ (oneParticleSchwartzToHilbert a f) (oneParticleSchwartzToHilbert a h)+
      ((‖oneParticleSchwartzToHilbert a g‖ : ℂ)^2)=_
  ring

theorem weylCoherentImage_zero_displacement (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    weylCoherentImage a 0 f=exponentialVector a f := by
  simp [weylCoherentImage]

theorem weylCoherentImage_vacuum (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    weylCoherentImage a g 0=normalizedCoherentVector a g := by
  simp only [weylCoherentImage,map_zero,inner_zero_right,sub_zero,zero_add,
    normalizedCoherentVector,Complex.ofReal_exp,Complex.ofReal_neg]
  congr 2 <;> push_cast <;> ring

end AASCKleinGordon
