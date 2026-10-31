import KGCoherentCreationComponents
import KGOriginalWeylCoreOperator

noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
open Filter
open scoped SchwartzMap Topology
namespace AASCKleinGordon

def coherentTruncationCore (f : 𝓢(Momentum,ℂ)) (N : ℕ) : FiniteParticleCore :=
  ∑ n∈Finset.range N,DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n (coherentSectorCore f n)

theorem coherentTruncationCore_embedding (a : Parameters) (f : 𝓢(Momentum,ℂ)) (N : ℕ) :
    finiteParticleCoreToFock a (coherentTruncationCore f N)=
      ∑ n∈Finset.range N,lp.single (E:=fun n => bosonicHilbertSector a n) 2 n (exponentialVector a f n) := by
  simp only [coherentTruncationCore,map_sum,finiteParticleCoreToFock_on_sector,
    coherentSectorCore_embedding,exponentialVector_component]

theorem coherentTruncationCore_tendsto (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    Tendsto (fun N : ℕ => finiteParticleCoreToFock a (coherentTruncationCore f N)) atTop
      (𝓝 (exponentialVector a f)) := by
  simpa only [coherentTruncationCore_embedding] using
    (lp.hasSum_single (by norm_num : (2 : ENNReal)≠⊤) (exponentialVector a f)).tendsto_sum_nat

theorem coherentTruncationCore_creation (a : Parameters) (g f : 𝓢(Momentum,ℂ)) (N : ℕ) :
    finiteParticleCoreToFock a (creationCore g (coherentTruncationCore f N))=
      ∑ n∈Finset.range N,lp.single (E:=fun n => bosonicHilbertSector a n) 2 (n+1)
        (coherentCreationTangent a g f (n+1)) := by
  simp only [coherentTruncationCore,map_sum,creationCore_lof,finiteParticleCoreToFock_on_sector,
    coherentCreationTangent_succ_component]

theorem coherentTruncationCore_annihilation (a : Parameters) (g f : 𝓢(Momentum,ℂ)) (N : ℕ) :
    finiteParticleCoreToFock a (annihilationCore a g (coherentTruncationCore f (N+1)))=
      inner ℂ (oneParticleSchwartzToHilbert a g) (oneParticleSchwartzToHilbert a f) •
        finiteParticleCoreToFock a (coherentTruncationCore f N) := by
  simp only [coherentTruncationCore,map_sum]
  rw [Finset.sum_range_succ']
  simp only [annihilationCore_lof_zero,map_zero,add_zero,annihilationCore_lof_succ,
    annihilation_coherentSectorCore,map_smul,finiteParticleCoreToFock_on_sector]
  rw [Finset.smul_sum]

theorem coherentTruncationCore_creation_tendsto (a : Parameters) (g f : 𝓢(Momentum,ℂ)) :
    Tendsto (fun N : ℕ => finiteParticleCoreToFock a (creationCore g (coherentTruncationCore f N)))
      atTop (𝓝 (coherentCreationTangent a g f)) := by
  have hs:=lp.hasSum_single (by norm_num : (2 : ENNReal)≠⊤) (coherentCreationTangent a g f)
  have hh : HasSum (fun n : ℕ => lp.single (E:=fun n => bosonicHilbertSector a n) 2 (n+1)
      (coherentCreationTangent a g f (n+1))) (coherentCreationTangent a g f) := by
    apply (hasSum_nat_add_iff (f:=fun i : ℕ => lp.single
      (E:=fun n => bosonicHilbertSector a n) 2 i (coherentCreationTangent a g f i)) 1).mpr
    simpa only [Finset.sum_range_one,coherentCreationTangent_zero_component,lp.single_zero,add_zero] using hs
  simpa only [coherentTruncationCore_creation] using hh.tendsto_sum_nat

theorem coherentTruncationCore_annihilation_tendsto (a : Parameters) (g f : 𝓢(Momentum,ℂ)) :
    Tendsto (fun N : ℕ => finiteParticleCoreToFock a
      (annihilationCore a g (coherentTruncationCore f (N+1)))) atTop
      (𝓝 (inner ℂ (oneParticleSchwartzToHilbert a g) (oneParticleSchwartzToHilbert a f) • exponentialVector a f)) := by
  simp_rw [coherentTruncationCore_annihilation]
  exact (coherentTruncationCore_tendsto a f).const_smul _

end AASCKleinGordon
