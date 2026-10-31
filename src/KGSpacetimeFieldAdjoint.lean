import KGSpacetimeFieldForms
import KGFockAdjointInclusions

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

theorem fockSpacetimeField_formalAdjoint (a : Parameters) (s : ℝ)
    (h : 𝓢(Spacetime,ℂ)) :
    (fockSpacetimeField a s h).IsFormalAdjoint
      (fockSpacetimeField a s (conjugateSchwartzCLM h)) := by
  intro u v
  let x := (fockCoreDomainEquiv a).symm u
  let y := (fockCoreDomainEquiv a).symm v
  have hu : u = includedFockCore a x := ((fockCoreDomainEquiv a).apply_symm_apply u).symm
  have hv : v = includedFockCore a y := ((fockCoreDomainEquiv a).apply_symm_apply v).symm
  rw [hu, hv, fockSpacetimeField_on_original_core, fockSpacetimeField_on_original_core]
  exact spacetimeFieldCore_adjoint_test a s h x y

theorem fockSpacetimeField_le_conjugate_adjoint (a : Parameters) (s : ℝ)
    (h : 𝓢(Spacetime,ℂ)) :
    fockSpacetimeField a s h ≤
      (fockSpacetimeField a s (conjugateSchwartzCLM h)).adjoint :=
  (fockSpacetimeField_formalAdjoint a s h).symm.le_adjoint
    (finiteParticleCoreToFock_dense a)

theorem fockSpacetimeField_closable (a : Parameters) (s : ℝ)
    (h : 𝓢(Spacetime,ℂ)) :
    (fockSpacetimeField a s h).IsClosable :=
  LinearPMap.isClosable_iff_exists_closed_extension.mpr
    ⟨(fockSpacetimeField a s (conjugateSchwartzCLM h)).adjoint,
      LinearPMap.adjoint_isClosed (finiteParticleCoreToFock_dense a),
      fockSpacetimeField_le_conjugate_adjoint a s h⟩

theorem fockSpacetimeField_real_test_formalSelfAdjoint (a : Parameters) (s : ℝ)
    (h : 𝓢(Spacetime,ℂ)) (hh : conjugateSchwartzCLM h = h) :
    (fockSpacetimeField a s h).IsFormalAdjoint (fockSpacetimeField a s h) := by
  simpa only [hh] using fockSpacetimeField_formalAdjoint a s h

end AASCKleinGordon
