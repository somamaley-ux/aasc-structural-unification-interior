import KGWeylCoherentCoreGenerator
import KGSpacetimeFieldAdjoint

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

def originalWeylCoreGenerator (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    FiniteParticleCore →ₗ[ℂ] FiniteParticleCore :=
  (-Complex.I) • (creationCore g-annihilationCore a g)

def originalWeylField (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    FockHilbert a →ₗ.[ℂ] FockHilbert a where
  domain:=fockCoreDomain a
  toFun:=((finiteParticleCoreToFock a).comp (originalWeylCoreGenerator a g)).comp
    (fockCoreDomainEquiv a).symm.toLinearMap

theorem originalWeylField_on_original_core (a : Parameters) (g : 𝓢(Momentum,ℂ))
    (u : FiniteParticleCore) :
    originalWeylField a g (includedFockCore a u)=
      finiteParticleCoreToFock a (originalWeylCoreGenerator a g u) := by
  change finiteParticleCoreToFock a (originalWeylCoreGenerator a g
    ((fockCoreDomainEquiv a).symm (fockCoreDomainEquiv a u)))=_
  rw [LinearEquiv.symm_apply_apply]

theorem originalWeylCoreGenerator_real_label (a : Parameters) (s : ℝ) (h : realSpacetimeTestSpace) :
    originalWeylCoreGenerator a (realFieldWeylLabelCLM a s h)=spacetimeFieldCore a s h.val := by
  rw [originalWeylCoreGenerator,imaginary_creation_annihilation_difference,smul_smul]
  simp only [neg_mul,Complex.I_mul_I,neg_neg,one_smul]

theorem originalWeylField_real_label (a : Parameters) (s : ℝ) (h : realSpacetimeTestSpace) :
    originalWeylField a (realFieldWeylLabelCLM a s h)=fockSpacetimeField a s h.val := by
  unfold originalWeylField fockSpacetimeField
  rw [originalWeylCoreGenerator_real_label]

theorem originalWeylField_symmetric (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    (originalWeylField a g).IsFormalAdjoint (originalWeylField a g) := by
  obtain ⟨h,hh⟩:=realFieldWeylLabel_surjective a 1 (by norm_num) g
  rw [← hh,originalWeylField_real_label]
  exact fockSpacetimeField_real_test_formalSelfAdjoint a 1 h.val
    ((mem_realSpacetimeTestSpace h.val).mp h.property)

theorem originalWeylField_closable (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    (originalWeylField a g).IsClosable :=
  LinearPMap.isClosable_iff_exists_closed_extension.mpr
    ⟨(originalWeylField a g).adjoint,
      LinearPMap.adjoint_isClosed (finiteParticleCoreToFock_dense a),
      (originalWeylField_symmetric a g).le_adjoint (finiteParticleCoreToFock_dense a)⟩

end AASCKleinGordon
