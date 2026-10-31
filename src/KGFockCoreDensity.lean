import KGBosonicCoreDensity
import KGFockCoreOccupation

noncomputable section
open Filter
open scoped ENNReal
namespace AASCKleinGordon

theorem fock_single_mem_core_closure (a : Parameters) (n : ℕ) (f : bosonicHilbertSector a n) :
    lp.single 2 n f ∈ (LinearMap.range (finiteParticleCoreToFock a)).topologicalClosure := by
  let S := (LinearMap.range (finiteParticleCoreToFock a)).topologicalClosure
  have hc : IsClosed {f : bosonicHilbertSector a n | lp.single 2 n f ∈ S} :=
    (LinearMap.range (finiteParticleCoreToFock a)).isClosed_topologicalClosure.preimage
      (lp.singleContinuousLinearMap ℂ (fun k : ℕ => bosonicHilbertSector a k) 2 n).continuous
  have hs : Set.range (bosonicCoreToSector a n) ⊆
      {f : bosonicHilbertSector a n | lp.single 2 n f ∈ S} := by
    rintro z ⟨g,rfl⟩
    apply (LinearMap.range (finiteParticleCoreToFock a)).le_topologicalClosure
    exact ⟨DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n g,finiteParticleCoreToFock_on_sector a n g⟩
  exact closure_minimal hs hc ((bosonicCoreToSector_dense a n) f)

theorem finiteParticleCoreToFock_dense (a : Parameters) : DenseRange (finiteParticleCoreToFock a) := by
  intro f
  apply (LinearMap.range (finiteParticleCoreToFock a)).isClosed_topologicalClosure.mem_of_tendsto
    (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞)≠⊤) f)
  exact Eventually.of_forall (fun s =>
    (LinearMap.range (finiteParticleCoreToFock a)).topologicalClosure.sum_mem
      (fun n _ => fock_single_mem_core_closure a n (f n)))

end AASCKleinGordon
