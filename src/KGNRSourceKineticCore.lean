import KGNRSourceCoreCoordinates
import KGSpatialKineticDomain

/-! The unchanged original one-core lies in the maximal kinetic domain.
Its kinetic image is constructed on Schwartz coordinates and compared by the
actual weighted momentum and physical Fourier maps. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon
theorem kg_nr_weighted_unitary_ae (a : Parameters) (f : OneParticleHilbert a) :
    kgWeightedMomentumUnitary a f =ᵐ[volume] (fun p => (kgWignerRoot a p : ℂ)*f p) :=
  kg_weighted_momentum_forward_ae a f

attribute [local irreducible] kgIsolatedMomentumUnitary kgWeightedMomentumUnitary
  kgPhysicalSpatialUnitary kgOriginalSpatialCoreEquiv kgNRFreeMomentumGenerator

theorem kg_nr_kinetic_temperate (a : Parameters) :
    (kgNRKineticEnergy a).HasTemperateGrowth := by
  have hp (j : Fin 3) : (fun p : Momentum => p j).HasTemperateGrowth :=
    (ContinuousLinearMap.proj j : Momentum →L[ℝ] ℝ).hasTemperateGrowth
  have h := (((hp 0).pow 2).add ((hp 1).pow 2)).add ((hp 2).pow 2)
  convert h.mul (Function.HasTemperateGrowth.const (2*a.mass)⁻¹) using 1

theorem kg_nr_kinetic_complex_temperate (a : Parameters) :
    (fun p => (kgNRKineticEnergy a p : ℂ)).HasTemperateGrowth :=
  Complex.ofRealCLM.hasTemperateGrowth.comp (kg_nr_kinetic_temperate a)

def kgNRSchwartzKinetic (a : Parameters) : 𝓢(Momentum,ℂ) →L[ℂ] 𝓢(Momentum,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun p => (kgNRKineticEnergy a p : ℂ))

theorem kg_nr_schwartz_kinetic_apply (a : Parameters) (f : 𝓢(Momentum,ℂ)) (p : Momentum) :
    kgNRSchwartzKinetic a f p = (kgNRKineticEnergy a p : ℂ)*f p :=
  SchwartzMap.smulLeftCLM_apply_apply (kg_nr_kinetic_complex_temperate a) f p

theorem kg_nr_weighted_schwartz_kinetic_graph (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    (kgWeightedMomentumUnitary a (oneParticleSchwartzToHilbert a f),
      kgWeightedMomentumUnitary a (oneParticleSchwartzToHilbert a (kgNRSchwartzKinetic a f))) ∈
      (kgNRFreeMomentumGenerator a).graph := by
  rw [kgNRFreeMomentumGenerator,Multiplication.realMultiplication_mem_graph]
  filter_upwards [kg_nr_weighted_unitary_ae a (oneParticleSchwartzToHilbert a f),
    kg_nr_weighted_unitary_ae a (oneParticleSchwartzToHilbert a (kgNRSchwartzKinetic a f)),
    (kg_wigner_ae a).mp (f.coeFn_toLp 2 (wignerMeasure a)),
    (kg_wigner_ae a).mp ((kgNRSchwartzKinetic a f).coeFn_toLp 2 (wignerMeasure a))]
    with p hf hg hs ht
  change (oneParticleSchwartzToHilbert a f) p=f p at hs
  change (oneParticleSchwartzToHilbert a (kgNRSchwartzKinetic a f)) p=
    kgNRSchwartzKinetic a f p at ht
  rw [hf,hg,hs,ht,kg_nr_schwartz_kinetic_apply]
  ring

def kgNROriginalOneCoreKinetic (a : Parameters) (x : kgOriginalOneCore a) : kgOriginalOneCore a :=
  kgOriginalOneCoreOfSchwartz a (kgNRSchwartzKinetic a (kgOriginalOneCoreCoordinates a x))

theorem kg_nr_original_one_core_momentum_graph (a : Parameters) (x : kgOriginalOneCore a) :
    (kgIsolatedMomentumUnitary a (kgOriginalOneCoreToIsolated a x),
      kgIsolatedMomentumUnitary a
        (kgOriginalOneCoreToIsolated a (kgNROriginalOneCoreKinetic a x))) ∈
      (kgNRFreeMomentumGenerator a).graph := by
  have hc : kgOriginalOneCoreCoordinates a (kgNROriginalOneCoreKinetic a x) =
      kgNRSchwartzKinetic a (kgOriginalOneCoreCoordinates a x) :=
    kg_original_one_core_coordinates_of_schwartz a _
  have hg := (kg_original_one_core_momentum_coordinates a (kgNROriginalOneCoreKinetic a x)).trans
    (congrArg (fun f : 𝓢(Momentum,ℂ) => kgWeightedMomentumUnitary a
      (oneParticleSchwartzToHilbert a f)) hc)
  have hp :
      (kgIsolatedMomentumUnitary a (kgOriginalOneCoreToIsolated a x),
        kgIsolatedMomentumUnitary a (kgOriginalOneCoreToIsolated a (kgNROriginalOneCoreKinetic a x))) =
      (kgWeightedMomentumUnitary a (oneParticleSchwartzToHilbert a (kgOriginalOneCoreCoordinates a x)),
        kgWeightedMomentumUnitary a (oneParticleSchwartzToHilbert a
          (kgNRSchwartzKinetic a (kgOriginalOneCoreCoordinates a x)))) :=
    Prod.ext (kg_original_one_core_momentum_coordinates a x) hg
  exact Eq.mpr (congrArg (fun z : KGNRMomentumHilbert × KGNRMomentumHilbert =>
    z ∈ (kgNRFreeMomentumGenerator a).graph) hp)
    (kg_nr_weighted_schwartz_kinetic_graph a (kgOriginalOneCoreCoordinates a x))

theorem kg_original_one_core_spatial_formula (a : Parameters) (x : kgOriginalOneCore a) :
    kgOriginalOneCoreSpatialEmbedding a x =
      kgPhysicalSpatialUnitary a
        (kgIsolatedMomentumUnitary a (kgOriginalOneCoreToIsolated a x)) := rfl

theorem kg_nr_original_one_core_spatial_graph (a : Parameters) (x : kgOriginalOneCore a) :
    (kgOriginalOneCoreSpatialEmbedding a x,
      kgOriginalOneCoreSpatialEmbedding a (kgNROriginalOneCoreKinetic a x)) ∈
      (kgNRSpatialKinetic a).graph := by
  have hf := (congrArg (kgPhysicalSpatialUnitary a).symm
    (kg_original_one_core_spatial_formula a x)).trans
      ((kgPhysicalSpatialUnitary a).symm_apply_apply _)
  have hg := (congrArg (kgPhysicalSpatialUnitary a).symm
    (kg_original_one_core_spatial_formula a (kgNROriginalOneCoreKinetic a x))).trans
      ((kgPhysicalSpatialUnitary a).symm_apply_apply _)
  have hp :
      ((kgPhysicalSpatialUnitary a).symm (kgOriginalOneCoreSpatialEmbedding a x),
        (kgPhysicalSpatialUnitary a).symm
          (kgOriginalOneCoreSpatialEmbedding a (kgNROriginalOneCoreKinetic a x))) =
      (kgIsolatedMomentumUnitary a (kgOriginalOneCoreToIsolated a x),
        kgIsolatedMomentumUnitary a (kgOriginalOneCoreToIsolated a (kgNROriginalOneCoreKinetic a x))) :=
    Prod.ext hf hg
  have h := Eq.mpr (congrArg (fun z : KGNRMomentumHilbert × KGNRMomentumHilbert =>
    z ∈ (kgNRFreeMomentumGenerator a).graph) hp)
      (kg_nr_original_one_core_momentum_graph a x)
  exact (kg_unitary_transport_graph (kgPhysicalSpatialUnitary a)
    (kgNRFreeMomentumGenerator a) _ _).mpr h

theorem kg_original_spatial_core_mem_maximal_kinetic_domain (a : Parameters)
    (f : kgOriginalSpatialCore a) : f.val ∈ (kgNRSpatialKinetic a).domain := by
  obtain ⟨x,hx⟩ := f.prop
  rw [← hx]
  exact LinearPMap.mem_domain_of_mem_graph (kg_nr_original_one_core_spatial_graph a x)

theorem kg_original_spatial_core_kinetic_image (a : Parameters)
    (f : kgOriginalSpatialCore a) :
    kgNRSpatialKinetic a ⟨f.val,kg_original_spatial_core_mem_maximal_kinetic_domain a f⟩ ∈
      kgOriginalSpatialCore a := by
  obtain ⟨x,hx⟩ := f.prop
  have h := kg_nr_original_one_core_spatial_graph a x
  obtain ⟨u,hu,hv⟩ := (LinearPMap.mem_graph_iff _).mp h
  have hf : (⟨f.val,kg_original_spatial_core_mem_maximal_kinetic_domain a f⟩ :
      (kgNRSpatialKinetic a).domain) = u := Subtype.ext (hx.symm.trans hu.symm)
  rw [hf]
  exact ⟨kgNROriginalOneCoreKinetic a x,hv.symm⟩

theorem kg_original_spatial_core_weak_kinetic (a : Parameters)
    (f : kgOriginalSpatialCore a) :
    kgSpatialWeakKineticGraph a f.val
      (kgNRSpatialKinetic a ⟨f.val,kg_original_spatial_core_mem_maximal_kinetic_domain a f⟩) :=
  (kg_nr_spatial_kinetic_weak_graph a _ _).mp ((kgNRSpatialKinetic a).mem_graph
    ⟨f.val,kg_original_spatial_core_mem_maximal_kinetic_domain a f⟩)

end AASCKleinGordon
