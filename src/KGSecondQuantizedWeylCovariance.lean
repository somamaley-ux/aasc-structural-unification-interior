import KGPoincareCoherentCovariance

noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem coherentVacuumTangent_pair_inner (a : Parameters) (f g : 𝓢(Momentum,ℂ)) :
    inner ℂ (coherentVacuumTangent a f) (coherentVacuumTangent a g)=
      inner ℂ (oneParticleSchwartzToHilbert a f) (oneParticleSchwartzToHilbert a g) := by
  rw [coherentVacuumTangent,lp.inner_single_left]
  change inner ℂ (coherentSector a f 1) (coherentSector a g 1)=_
  rw [coherentSector_inner]
  norm_num

/-- Derivative uniqueness recovers exact one-particle inner products from
actual second quantization; no injectivity of complex exp is used. -/
theorem secondQuantized_label_inner (a : Parameters)
    (U : FockHilbert a ≃ₗᵢ[ℂ] FockHilbert a)
    (R : 𝓢(Momentum,ℂ) →L[ℂ] 𝓢(Momentum,ℂ))
    (hU : ∀ f, U (exponentialVector a f)=exponentialVector a (R f))
    (f g : 𝓢(Momentum,ℂ)) :
    inner ℂ (oneParticleSchwartzToHilbert a (R f)) (oneParticleSchwartzToHilbert a (R g))=
      inner ℂ (oneParticleSchwartzToHilbert a f) (oneParticleSchwartzToHilbert a g) := by
  have ht : ∀ f, U (coherentVacuumTangent a f)=coherentVacuumTangent a (R f) := by
    intro f
    have hh:= (U.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
      (exponentialVector_real_line_hasDerivAt_zero a f)
    have hh' : HasDerivAt (fun t : ℝ => U (exponentialVector a ((t : ℂ) • f)))
        (U (coherentVacuumTangent a f)) 0 := by
      simpa only [Function.comp_def,ContinuousLinearMap.coe_restrictScalars'] using hh
    simp only [hU,map_smul] at hh'
    exact hh'.unique (exponentialVector_real_line_hasDerivAt_zero a (R f))
  rw [← coherentVacuumTangent_pair_inner,← ht f,← ht g,U.inner_map_map,
    coherentVacuumTangent_pair_inner]

theorem secondQuantized_weyl_intertwine (a : Parameters)
    (U : FockHilbert a ≃ₗᵢ[ℂ] FockHilbert a)
    (R : 𝓢(Momentum,ℂ) →L[ℂ] 𝓢(Momentum,ℂ))
    (hU : ∀ f, U (exponentialVector a f)=exponentialVector a (R f))
    (g : 𝓢(Momentum,ℂ)) :
    U.toContinuousLinearEquiv.toContinuousLinearMap.comp (weylOperator a g)=
      (weylOperator a (R g)).comp U.toContinuousLinearEquiv.toContinuousLinearMap := by
  have hn : ‖oneParticleSchwartzToHilbert a (R g)‖^2=
      ‖oneParticleSchwartzToHilbert a g‖^2 := by
    have hh:=secondQuantized_label_inner a U R hU g g
    rw [inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K] at hh
    exact_mod_cast hh
  apply continuousLinearMap_eq_on_exponentialVectors a
  intro f
  change U (weylOperator a g (exponentialVector a f))=
    weylOperator a (R g) (U (exponentialVector a f))
  rw [weylOperator_exponentialVector,weylCoherentImage,map_smul,hU,hU,
    weylOperator_exponentialVector,weylCoherentImage,hn,
    secondQuantized_label_inner a U R hU,map_add]

theorem fockPoincare_weyl_intertwine (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (g : 𝓢(Momentum,ℂ)) (v : FockHilbert a) :
    fockPoincareUnitary a b L (weylOperator a g v)=
      weylOperator a (poincareSchwartzCLM a b L g) (fockPoincareUnitary a b L v) := by
  exact congrArg (fun T : FockHilbert a →L[ℂ] FockHilbert a => T v)
    (secondQuantized_weyl_intertwine a (fockPoincareUnitary a b L)
      (poincareSchwartzCLM a b L) (fockPoincare_exponentialVector a b L) g)

theorem fockPoincare_weyl_conjugation (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (g : 𝓢(Momentum,ℂ)) (v : FockHilbert a) :
    fockPoincareUnitary a b L (weylOperator a g ((fockPoincareUnitary a b L).symm v))=
      weylOperator a (poincareSchwartzCLM a b L g) v := by
  rw [fockPoincare_weyl_intertwine,LinearIsometryEquiv.apply_symm_apply]

end AASCKleinGordon
