import KGFockBoundedMultipliers
import KGFockCoreSpatialCharges

/-! Actual countable-Fock momentum/energy multiplication. The full graph is
sectorwise almost-everywhere multiplication, and its domain requires the
output family to be square summable. Equality with the original core's
closure, translation generators and total-EMT attachment remain separate. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
namespace AASCKleinGordon

variable (a : Parameters) (v : ∀ n,ParticleConfiguration n → ℝ)
variable (hv : ∀ n,Measurable (v n))
variable (hi : ∀ n (σ : Equiv.Perm (Fin n)) x,v n (particlePermutation n σ x)=v n x)

def fockRealMultiplication : FockHilbert a →ₗ.[ℂ] FockHilbert a :=
  BoundedPair.operator (fockCoefficientA a v hv hi) (fockCoefficientB a v hv hi)
    (fockCoefficientB_injective a v hv hi)

theorem fockRealMultiplication_selfAdjoint : IsSelfAdjoint (fockRealMultiplication a v hv hi) :=
  BoundedPair.operator_selfAdjoint _ _ _ (fockCoefficients_commute a v hv hi)
    (fockCoefficients_normalized a v hv hi) (fockCoefficientB_symmetric a v hv hi)
    (fockCoefficientA_symmetric a v hv hi)

theorem fockRealMultiplication_closed : (fockRealMultiplication a v hv hi).IsClosed :=
  BoundedPair.operator_closed _ _ _

theorem fockRealMultiplication_dense :
    Dense ((fockRealMultiplication a v hv hi).domain : Set (FockHilbert a)) :=
  BoundedPair.operator_dense _ _ _ (fockCoefficients_commute a v hv hi)
    (fockCoefficientB_symmetric a v hv hi)

theorem fockRealMultiplication_mem_graph (f g : FockHilbert a) :
    (f,g) ∈ (fockRealMultiplication a v hv hi).graph ↔
      ∀ n,(g n).val=ᵐ[particleMeasure a n] (fun x => (v n x : ℂ)*(f n).val x) := by
  rw [fockRealMultiplication,BoundedPair.operator_graph,BoundedPair.mem_relation]
  constructor
  · intro h n
    have hn := congrArg (fun z : FockHilbert a => z n) h
    have hg : (f n,g n) ∈ (bosonicRealMultiplication a n (v n) (hv n) (hi n)).graph := by
      rw [bosonicRealMultiplication,Multiplication.subspaceRealMultiplication,
        BoundedPair.operator_graph,BoundedPair.mem_relation]
      exact hn
    exact (bosonicRealMultiplication_mem_graph _ _ _ _ _ _ _).1 hg
  · intro h
    apply lp.ext
    funext n
    have hg := (bosonicRealMultiplication_mem_graph a n (v n) (hv n) (hi n) (f n) (g n)).2 (h n)
    rw [bosonicRealMultiplication,Multiplication.subspaceRealMultiplication,
      BoundedPair.operator_graph,BoundedPair.mem_relation] at hg
    exact hg

theorem fockRealMultiplication_exact_domain (f : FockHilbert a) :
    f ∈ (fockRealMultiplication a v hv hi).domain ↔
      ∃ g : ∀ n,bosonicHilbertSector a n,Memℓp g 2 ∧
        ∀ n,(g n).val=ᵐ[particleMeasure a n] (fun x => (v n x : ℂ)*(f n).val x) := by
  constructor
  · intro hf
    let g := fockRealMultiplication a v hv hi ⟨f,hf⟩
    exact ⟨g,lp.memℓp g,(fockRealMultiplication_mem_graph a v hv hi f g).1
      ((fockRealMultiplication a v hv hi).mem_graph ⟨f,hf⟩)⟩
  · rintro ⟨g,hg,hval⟩
    exact LinearPMap.mem_domain_of_mem_graph
      ((fockRealMultiplication_mem_graph a v hv hi f ⟨g,hg⟩).2 hval)

def fockMaximalSpatialMomentum (a : Parameters) (j : Fin 3) :
    FockHilbert a →ₗ.[ℂ] FockHilbert a :=
  fockRealMultiplication a (fun n => totalMomentumCLM n j)
    (fun n => (totalMomentumCLM n j).measurable) (fun n => totalMomentum_particlePermutation n j)

def fockMaximalEnergy (a : Parameters) : FockHilbert a →ₗ.[ℂ] FockHilbert a :=
  fockRealMultiplication a (particleTotalEnergy a)
    (fun n => (particleTotalEnergy_continuous a n).measurable) (particleTotalEnergy_particlePermutation a)

theorem fockMaximalSpatialMomentum_selfAdjoint (a : Parameters) (j : Fin 3) :
    IsSelfAdjoint (fockMaximalSpatialMomentum a j) := fockRealMultiplication_selfAdjoint _ _ _ _

theorem fockMaximalEnergy_selfAdjoint (a : Parameters) :
    IsSelfAdjoint (fockMaximalEnergy a) := fockRealMultiplication_selfAdjoint _ _ _ _

theorem fockMaximalSpatialMomentum_graph_on_original_core
    (a : Parameters) (j : Fin 3) (f : FiniteParticleCore) :
    (finiteParticleCoreToFock a f,finiteParticleCoreToFock a (coreSpatialMomentum j f)) ∈
      (fockMaximalSpatialMomentum a j).graph := by
  apply (fockRealMultiplication_mem_graph _ _ _ _ _ _).2
  intro n
  simp only [finiteParticleCoreToFock_component]
  change (bosonicCoreToSector a n (sectorSpatialMomentum n j (f n))).val=ᵐ[particleMeasure a n]
    (fun x => (totalMomentumCLM n j x : ℂ)*(bosonicCoreToSector a n (f n)).val x)
  exact (bosonicRealMultiplication_mem_graph _ _ _ _ _ _ _).1
    (bosonicMaximalSpatialMomentum_graph_on_original_core a n j (f n))

theorem fockCoreSpatialCharge_le_maximal (a : Parameters) (j : Fin 3) :
    fockCoreSpatialCharge a j ≤ fockMaximalSpatialMomentum a j := by
  apply LinearPMap.le_of_le_graph
  intro z hz
  obtain ⟨f,rfl⟩ := (LinearPMap.mem_graph_iff' _).mp hz
  let u := (fockCoreDomainEquiv a).symm f
  have hf : f=includedFockCore a u := ((fockCoreDomainEquiv a).apply_symm_apply f).symm
  rw [hf,fockCoreSpatialCharge_on_original_core]
  exact fockMaximalSpatialMomentum_graph_on_original_core a j u

end AASCKleinGordon
