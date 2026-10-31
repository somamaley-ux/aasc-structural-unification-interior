import KGWeylRelations
import KGCoherentAnalytic

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

def CommutesWithWeyl (a : Parameters) (T : FockHilbert a →L[ℂ] FockHilbert a) : Prop :=
  ∀ g : 𝓢(Momentum,ℂ),T * weylOperator a g=weylOperator a g * T

theorem weyl_commutant_vacuum_coherent_identity (a : Parameters)
    (T : FockHilbert a →L[ℂ] FockHilbert a) (hT : CommutesWithWeyl a T)
    (g : 𝓢(Momentum,ℂ)) :
    inner ℂ (fockVacuum a) (T (exponentialVector a g))=
      inner ℂ (exponentialVector a (-g)) (T (fockVacuum a)) := by
  let c : ℂ:=(Real.exp (-‖oneParticleSchwartzToHilbert a g‖^2/2) : ℂ)
  have hc : c≠0:=by
    exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hcstar : starRingEnd ℂ c=c:=Complex.conj_ofReal _
  have hv : normalizedCoherentVector a g=c • exponentialVector a g:=rfl
  have hvn : normalizedCoherentVector a (-g)=c • exponentialVector a (-g) := by
    simp only [normalizedCoherentVector,map_neg,norm_neg,c]
  have hh:=congrArg (fun A : FockHilbert a →L[ℂ] FockHilbert a =>
    inner ℂ (fockVacuum a) (A (fockVacuum a))) (hT g)
  change inner ℂ (fockVacuum a) (T (weylOperator a g (fockVacuum a)))=
    inner ℂ (fockVacuum a) (weylOperator a g (T (fockVacuum a))) at hh
  have hadj:=(weylOperator a g).adjoint_inner_left (T (fockVacuum a)) (fockVacuum a)
  rw [weylOperator_adjoint] at hadj
  rw [weylOperator_vacuum,hv,map_smul,inner_smul_right,
    ← hadj,
    weylOperator_vacuum,hvn,inner_smul_left,hcstar] at hh
  exact mul_left_cancel₀ hc hh

theorem weyl_commutant_coherent_scalar_constant (a : Parameters)
    (T : FockHilbert a →L[ℂ] FockHilbert a) (hT : CommutesWithWeyl a T)
    (f : 𝓢(Momentum,ℂ)) :
    inner ℂ (fockVacuum a) (T (exponentialVector a f))=
      inner ℂ (fockVacuum a) (T (fockVacuum a)) := by
  let A : ℂ → ℂ:=fun z => inner ℂ (fockVacuum a) (T (exponentialVector a (z • f)))
  let B : ℂ → ℂ:=fun z => inner ℂ (T (fockVacuum a)) (exponentialVector a (z • (-f)))
  have ha : Differentiable ℂ A:=boundedCoherentScalar_differentiable a _ T f
  have hb : Differentiable ℂ B:=coherentScalar_differentiable a _ (-f)
  have hab (z : ℂ) : A z=star (B z) := by
    dsimp [A,B]
    rw [weyl_commutant_vacuum_coherent_identity a T hT]
    simp only [smul_neg,inner_conj_symm]
  have hh:=differentiable_eq_conj_forces_constant A B ha hb hab 1 0
  simpa only [A,one_smul,zero_smul,exponentialVector_zero] using hh

theorem exponentialVector_inner_vacuum (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    inner ℂ (exponentialVector a f) (fockVacuum a)=1 := by
  rw [← exponentialVector_zero,exponentialVector_inner]
  simp

theorem weyl_commutant_vacuum_eigenvector (a : Parameters)
    (T : FockHilbert a →L[ℂ] FockHilbert a) (hT : CommutesWithWeyl a T) :
    T (fockVacuum a)=inner ℂ (fockVacuum a) (T (fockVacuum a)) • fockVacuum a := by
  apply sub_eq_zero.mp
  apply exponentialVector_total a
  intro f
  apply inner_eq_zero_symm.mpr
  rw [inner_sub_right,inner_smul_right,exponentialVector_inner_vacuum,mul_one]
  have hh:=weyl_commutant_vacuum_coherent_identity a T hT (-f)
  rw [neg_neg,weyl_commutant_coherent_scalar_constant a T hT] at hh
  exact sub_eq_zero.mpr hh.symm

/-- Every bounded operator commuting with the constructed global Weyl family
is scalar. No preservation of the unbounded-field core is assumed. -/
theorem weyl_commutant_is_scalar (a : Parameters)
    (T : FockHilbert a →L[ℂ] FockHilbert a) (hT : CommutesWithWeyl a T) :
    T=inner ℂ (fockVacuum a) (T (fockVacuum a)) •
      ContinuousLinearMap.id ℂ (FockHilbert a) := by
  apply continuousLinearMap_eq_on_exponentialVectors a
  intro f
  let c : ℂ:=(Real.exp (-‖oneParticleSchwartzToHilbert a f‖^2/2) : ℂ)
  have hc : c≠0:=by
    exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hh:=congrArg (fun A : FockHilbert a →L[ℂ] FockHilbert a => A (fockVacuum a)) (hT f)
  change T (weylOperator a f (fockVacuum a))=weylOperator a f (T (fockVacuum a)) at hh
  rw [weyl_commutant_vacuum_eigenvector a T hT,map_smul,weylOperator_vacuum] at hh
  change T (c • exponentialVector a f)=
    inner ℂ (fockVacuum a) (T (fockVacuum a)) • (c • exponentialVector a f) at hh
  rw [map_smul,smul_comm] at hh
  exact (smul_right_injective _ hc) hh

end AASCKleinGordon
