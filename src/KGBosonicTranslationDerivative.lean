import L2TranslationDerivative
import KGFockTranslationGroups

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AASCKleinGordon

theorem bosonicPhase_hasDerivAt_zero_of_graph (a : Parameters) (n : ℕ)
    (v : ParticleConfiguration n → ℝ) (hv : Measurable v)
    (hi : ∀ (σ : Equiv.Perm (Fin n)) x,v (particlePermutation n σ x)=v x)
    (hbar : ℝ) (f g : bosonicHilbertSector a n)
    (hg : g.val=ᵐ[particleMeasure a n] (fun x => (v x : ℂ)*f.val x)) :
    HasDerivAt (fun t => bosonicPhaseMultiplier a n v hv hi hbar t f)
      (Translation.coefficient hbar • g) 0 := by
  have hgraph := (Multiplication.realMultiplication_mem_graph v f.val g.val).2 hg
  have hf := LinearPMap.mem_domain_of_mem_graph hgraph
  have he : Multiplication.realMultiplication v ⟨f.val,hf⟩=g.val :=
    LinearPMap.mem_graph_snd_inj _ ((Multiplication.realMultiplication v).mem_graph ⟨f.val,hf⟩) hgraph rfl
  have hd := Multiplication.phaseMultiplier_hasDerivAt_zero v hv hbar ⟨f.val,hf⟩
  rw [he] at hd
  rw [hasDerivAt_iff_tendsto_slope_zero]
  apply tendsto_subtype_rng.mpr
  exact hd.tendsto_slope_zero

theorem bosonicPhase_slope_bound_of_graph (a : Parameters) (n : ℕ)
    (v : ParticleConfiguration n → ℝ) (hv : Measurable v)
    (hi : ∀ (σ : Equiv.Perm (Fin n)) x,v (particlePermutation n σ x)=v x)
    (hbar t : ℝ) (f g : bosonicHilbertSector a n)
    (hg : g.val=ᵐ[particleMeasure a n] (fun x => (v x : ℂ)*f.val x)) :
    ‖(t⁻¹ : ℝ) • (bosonicPhaseMultiplier a n v hv hi hbar t f-f)‖≤
      ‖Translation.coefficient hbar‖*‖g‖ := by
  have hgraph := (Multiplication.realMultiplication_mem_graph v f.val g.val).2 hg
  have hf := LinearPMap.mem_domain_of_mem_graph hgraph
  have he : Multiplication.realMultiplication v ⟨f.val,hf⟩=g.val :=
    LinearPMap.mem_graph_snd_inj _ ((Multiplication.realMultiplication v).mem_graph ⟨f.val,hf⟩) hgraph rfl
  have hd := Multiplication.orbitSlope_norm_bound v hv hbar t ⟨f.val,hf⟩
  rw [he] at hd
  exact hd

end AASCKleinGordon
