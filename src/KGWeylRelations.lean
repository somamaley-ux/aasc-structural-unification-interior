import KGWeylBoundedOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

def weylPhase (a : Parameters) (g h : 𝓢(Momentum,ℂ)) : ℂ :=
  Complex.exp ((inner ℂ (oneParticleSchwartzToHilbert a h) (oneParticleSchwartzToHilbert a g)-
    inner ℂ (oneParticleSchwartzToHilbert a g) (oneParticleSchwartzToHilbert a h))/2)

theorem weylOperator_weylCoherentImage (a : Parameters) (g h f : 𝓢(Momentum,ℂ)) :
    weylOperator a g (weylCoherentImage a h f)=
      weylPhase a g h • weylCoherentImage a (g+h) f := by
  rw [weylCoherentImage,map_smul,weylOperator_exponentialVector]
  simp only [weylCoherentImage,weylPhase,smul_smul]
  rw [show (f+h)+g=f+(g+h) by abel]
  congr 1
  rw [← Complex.exp_add,← Complex.exp_add]
  congr 1
  have hn (u : OneParticleHilbert a) : ((‖u‖^2/2 : ℝ) : ℂ)=inner ℂ u u/2 := by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    change (‖u‖ : ℂ)^2/2=(‖u‖ : ℂ)^2/2
    rfl
  simp only [hn,map_add,inner_add_left,inner_add_right]
  ring

theorem weylOperator_mul (a : Parameters) (g h : 𝓢(Momentum,ℂ)) :
    weylOperator a g * weylOperator a h=weylPhase a g h • weylOperator a (g+h) := by
  apply continuousLinearMap_eq_on_exponentialVectors a
  intro f
  change weylOperator a g (weylOperator a h (exponentialVector a f))=_
  rw [weylOperator_exponentialVector,weylOperator_weylCoherentImage]
  simp only [ContinuousLinearMap.smul_apply,weylOperator_exponentialVector]

theorem weylPhase_neg_right (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    weylPhase a g (-g)=1 := by
  simp [weylPhase]

theorem weylOperator_mul_inverse (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    weylOperator a g * weylOperator a (-g)=1 := by
  rw [weylOperator_mul,weylPhase_neg_right,add_neg_cancel,one_smul,weylOperator_zero]
  rfl

theorem weylOperator_inverse_mul (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    weylOperator a (-g) * weylOperator a g=1 := by
  simpa only [neg_neg] using weylOperator_mul_inverse a (-g)

/-- The constructed bounded Weyl operators are actual unitaries of the same Fock space. -/
def weylUnitary (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    FockHilbert a ≃ₗᵢ[ℂ] FockHilbert a :=
  { weylIsometry a g with
    invFun := weylOperator a (-g)
    left_inv := fun u => by
      have h:=congrArg (fun T : FockHilbert a →L[ℂ] FockHilbert a => T u)
        (weylOperator_inverse_mul a g)
      exact h
    right_inv := fun u => by
      have h:=congrArg (fun T : FockHilbert a →L[ℂ] FockHilbert a => T u)
        (weylOperator_mul_inverse a g)
      exact h }

theorem weylOperator_inner (a : Parameters) (g : 𝓢(Momentum,ℂ)) (u v : FockHilbert a) :
    inner ℂ (weylOperator a g u) (weylOperator a g v)=inner ℂ u v :=
  (weylUnitary a g).inner_map_map u v

theorem weylOperator_adjoint (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    ContinuousLinearMap.adjoint (weylOperator a g)=weylOperator a (-g) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  have hi:=weylOperator_inner a g (weylOperator a (-g) x) y
  have hx:=congrArg (fun T : FockHilbert a →L[ℂ] FockHilbert a => T x)
    (weylOperator_mul_inverse a g)
  change weylOperator a g (weylOperator a (-g) x)=x at hx
  rw [hx] at hi
  exact hi.symm

end AASCKleinGordon
