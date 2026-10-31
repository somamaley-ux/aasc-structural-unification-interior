import SchwartzFiniteJetBanach
import BanachClosedSpanIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter Topology
open scoped SchwartzMap
namespace AASCKleinGordon



/-- The finite linear span of the ACTUAL previously constructed wavepacket tests. -/
def wickPurePairSpan : Submodule ℂ 𝓢(ParticleConfiguration 2,ℂ) :=
  Submodule.span ℂ (Set.range (fun p : 𝓢(Momentum,ℂ) × 𝓢(Momentum,ℂ) =>
    wickCovariantPairTest p.1 p.2))

theorem wick_pure_pair_mem_span (f g : 𝓢(Momentum,ℂ)) :
    wickCovariantPairTest f g∈wickPurePairSpan :=
  Submodule.subset_span ⟨(f,g),rfl⟩

def wickPurePairJetSpan (S : Finset (ℕ × ℕ)) :
    Submodule ℂ (WickFiniteJetBanach (ParticleConfiguration 2) S) :=
  wickPurePairSpan.map (wickFiniteSchwartzJetBanachCLM S).toLinearMap

/-- Honest integrability and pointwise pure-span membership imply closure only
for this Banach integral. This is not a premise asserting tensor density. -/
theorem wick_pure_pair_jet_integral_mem_closure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Finset (ℕ × ℕ))
    (F : X → WickFiniteJetBanach (ParticleConfiguration 2) S)
    (hF : Integrable F μ) (hmem : ∀ᵐ x ∂μ,F x∈wickPurePairJetSpan S) :
    (∫ x,F x ∂μ)∈(wickPurePairJetSpan S).topologicalClosure :=
  wick_integral_mem_closed_submodule μ _ (wickPurePairJetSpan S).isClosed_topologicalClosure
    F hF (hmem.mono (fun _ hx => (wickPurePairJetSpan S).le_topologicalClosure hx))

/-- Extract an actual finite pure-pair span element near the actual Banach integral. -/
theorem wick_pure_pair_jet_integral_approximation {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Finset (ℕ × ℕ))
    (F : X → WickFiniteJetBanach (ParticleConfiguration 2) S)
    (hF : Integrable F μ) (hmem : ∀ᵐ x ∂μ,F x∈wickPurePairJetSpan S)
    (ε : ℝ) (hε : 0<ε) :
    ∃ G∈wickPurePairSpan,‖wickFiniteSchwartzJetBanachCLM S G-∫ x,F x ∂μ‖<ε := by
  have hc := wick_pure_pair_jet_integral_mem_closure μ S F hF hmem
  obtain ⟨y,hy,hd⟩ := Metric.mem_closure_iff.mp hc ε hε
  obtain ⟨G,hG,hJG⟩ := hy
  refine ⟨G,hG,?_⟩
  change ‖(wickFiniteSchwartzJetBanachCLM S).toLinearMap G-∫ x,F x ∂μ‖<ε
  rw [hJG]
  have he : dist (∫ x,F x ∂μ) y=‖y-∫ x,F x ∂μ‖ := by
    rw [dist_eq_norm,norm_sub_rev]
  exact he ▸ hd

end AASCKleinGordon
