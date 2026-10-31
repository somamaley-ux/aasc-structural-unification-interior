import KGFockCoreAdjointness

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem fockCoreCreation_formalAdjoint (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    (fockCoreCreation a f).IsFormalAdjoint (fockCoreAnnihilation a f) :=
  fockCore_creation_annihilation_adjoint a f

theorem fockCoreCreation_le_annihilation_adjoint (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    fockCoreCreation a f ≤ (fockCoreAnnihilation a f).adjoint :=
  (fockCoreCreation_formalAdjoint a f).symm.le_adjoint (finiteParticleCoreToFock_dense a)

theorem fockCoreAnnihilation_le_creation_adjoint (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    fockCoreAnnihilation a f ≤ (fockCoreCreation a f).adjoint :=
  (fockCoreCreation_formalAdjoint a f).le_adjoint (finiteParticleCoreToFock_dense a)

theorem fockCoreCreation_closable (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    (fockCoreCreation a f).IsClosable :=
  LinearPMap.isClosable_iff_exists_closed_extension.mpr
    ⟨(fockCoreAnnihilation a f).adjoint,
      LinearPMap.adjoint_isClosed (finiteParticleCoreToFock_dense a),
      fockCoreCreation_le_annihilation_adjoint a f⟩

theorem fockCoreAnnihilation_closable (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    (fockCoreAnnihilation a f).IsClosable :=
  LinearPMap.isClosable_iff_exists_closed_extension.mpr
    ⟨(fockCoreCreation a f).adjoint,
      LinearPMap.adjoint_isClosed (finiteParticleCoreToFock_dense a),
      fockCoreAnnihilation_le_creation_adjoint a f⟩

end AASCKleinGordon
