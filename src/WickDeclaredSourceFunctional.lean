import WickPoincareRayTransport

noncomputable section
set_option maxHeartbeats 1500000
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

/-- Numeric adapter on actual FIRST acts. The full sum-valued ledger remains
separate, so failed finite requests receive no fictitious numeric output. -/
def wickKGFirstActOperationalIncidence (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    (Ω : Opens CoordinatePoint) : OperationalMetricIncidence Ω (WickKGFirstMetricAct Ω) where
  incident H δ := wickKGFirstTangent δ=H
  output := wickKGFirstOutput a s u
  total H := ⟨wickKGIdentityAct H,wick_KG_identity_tangent H⟩
  coherent H δ ε hδ hε := wick_KG_original_tangent_coherence a s u δ ε (hδ.trans hε.symm)
  add_compatible H K δ ε hδ hε := by
    obtain ⟨σ,tangent,output⟩ := wick_KG_original_addition_witness a s u δ ε
    exact ⟨σ,tangent.trans (congrArg₂ (·+·) hδ hε),output⟩
  smul_compatible r H δ hδ := by
    obtain ⟨σ,tangent,output⟩ := wick_KG_original_scaling_witness a s u δ r
    exact ⟨σ,tangent.trans (congrArg (r • ·) hδ),output⟩

theorem wick_KG_first_operational_response_original (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω) :
    operationalMetricResponse (wickKGFirstActOperationalIncidence a s u Ω) H=
      originalWickNativeRealMetricResponse a s u Ω H := by
  rw [operational_response_of_incident (wickKGFirstActOperationalIncidence a s u Ω)
    H (wickKGIdentityAct H) (wick_KG_identity_tangent H)]
  change wickKGFirstOutput a s u (wickKGIdentityAct H)=_
  rw [wick_KG_original_first_output_computed,wick_KG_identity_tangent]

theorem wick_KG_first_operational_compact_continuity (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) (K : Compacts CoordinatePoint)
    (hK : (K : Set CoordinatePoint)⊆Ω) :
    Continuous (operationalMetricResponse (wickKGFirstActOperationalIncidence a s u Ω) ∘
      TestFunction.ofSupportedIn hK) := by
  have same : operationalMetricResponse (wickKGFirstActOperationalIncidence a s u Ω)=
      originalWickNativeRealMetricResponse a s u Ω :=
    funext (wick_KG_first_operational_response_original a s u Ω)
  rw [same]
  exact (originalWickNativeRealMetricResponse a s u Ω).continuous.comp
    (TestFunction.continuous_ofSupportedIn hK)

def wickKGFirstOperationalFunctional (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    (Ω : Opens CoordinatePoint) : MetricSourceProbe Ω →L[ℝ] ℝ :=
  operationalMetricFunctional (wickKGFirstActOperationalIncidence a s u Ω)
    (wick_KG_first_operational_compact_continuity a s u Ω)

theorem wick_KG_first_operational_functional_same (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) :
    wickKGFirstOperationalFunctional a s u Ω=originalWickNativeRealMetricResponse a s u Ω := by
  ext H
  exact wick_KG_first_operational_response_original a s u Ω H

def wickKGChartOutput (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    {Ω : Opens CoordinatePoint} (D : Set (MetricSourceProbe Ω)) :
    WickKGOriginalProtocol Ω → WickKGOriginalReadout := by
  classical
  exact fun
    | .finite H => if H∈D then .finite (wickOriginalRealFiniteAction a s u H) else .failed
    | .first δ => .first (wickKGFirstOutput a s u δ)

theorem wick_KG_chart_base_is_original (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    (Ω : Opens CoordinatePoint) :
    wickKGChartOutput a s u (wickOriginalMetricNeighborhood Ω)=wickKGOriginalOutput a s u := by
  classical
  funext π
  cases π with
  | first δ => rfl
  | finite H =>
    by_cases h : H∈wickOriginalMetricNeighborhood Ω
    · simp only [wickKGChartOutput,wickKGOriginalOutput,if_pos h,dif_pos h,wickKGFiniteActionCarrier]
    · simp only [wickKGChartOutput,wickKGOriginalOutput,if_neg h,dif_neg h]

theorem wick_KG_chart_transport_is_original (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    (b : Spacetime) (L : ProperLorentzTransform) (Ω : Opens CoordinatePoint) :
    wickKGChartOutput a s u (wickTransportedMetricDomain b L Ω)=
      wickKGTransportedChartOutput a s u b L Ω := by
  classical
  funext π
  cases π with
  | first δ => rfl
  | finite H =>
    by_cases inside : H∈wickTransportedMetricDomain b L Ω
    · simp only [wickKGChartOutput,wickKGTransportedChartOutput,if_pos inside]
    · simp only [wickKGChartOutput,wickKGTransportedChartOutput,if_neg inside]

def wickKGChartMetResp (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    {Ω : Opens CoordinatePoint} (D : Set (MetricSourceProbe Ω))
    (H : MetricSourceProbe Ω) (z : ℝ) : Prop :=
  ∃ π,wickKGOriginalMetInc H π ∧ wickKGChartOutput a s u D π=.first z

theorem wick_KG_chart_response_graph (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    (Ω : Opens CoordinatePoint) (D : Set (MetricSourceProbe Ω)) (H : MetricSourceProbe Ω) (z : ℝ) :
    wickKGChartMetResp a s u D H z ↔ originalWickNativeRealMetricResponse a s u Ω H=z := by
  constructor
  · rintro ⟨π,⟨δ,incident,tangent⟩,output⟩
    change π=.first δ at incident
    subst π
    have first : wickKGFirstOutput a s u δ=z := WickKGOriginalReadout.first.inj output
    exact (congrArg (originalWickNativeRealMetricResponse a s u Ω) tangent).symm.trans
      ((wick_KG_original_first_output_computed a s u δ).symm.trans first)
  · intro same
    refine ⟨.first (wickKGIdentityAct H),⟨wickKGIdentityAct H,rfl,wick_KG_identity_tangent H⟩,?_⟩
    exact congrArg WickKGOriginalReadout.first
      ((wick_KG_original_first_output_computed a s u (wickKGIdentityAct H)).trans
        ((congrArg (originalWickNativeRealMetricResponse a s u Ω) (wick_KG_identity_tangent H)).trans same))

theorem wick_KG_declared_protocol_constructor_complete (Ω : Opens CoordinatePoint)
    (π : WickKGOriginalProtocol Ω) :
    (∃ H,π=.finite H) ∨ (∃ δ,π=.first δ) := by
  cases π with
  | finite H => exact Or.inl ⟨H,rfl⟩
  | first δ => exact Or.inr ⟨δ,rfl⟩

theorem wick_KG_chart_failure_exact (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    (Ω : Opens CoordinatePoint) (D : Set (MetricSourceProbe Ω)) (π : WickKGOriginalProtocol Ω) :
    wickKGChartOutput a s u D π=.failed ↔ ∃ H,π=.finite H ∧ H∉D := by
  classical
  cases π with
  | first δ => simp only [wickKGChartOutput,reduceCtorEq,false_iff]; rintro ⟨H,h,_⟩; cases h
  | finite H =>
    by_cases inside : H∈D
    · simp only [wickKGChartOutput,if_pos inside,reduceCtorEq,false_iff]
      rintro ⟨K,same,outside⟩
      have equal := WickKGOriginalProtocol.finite.inj same
      exact outside (equal ▸ inside)
    · constructor
      · intro _; exact ⟨H,rfl,inside⟩
      · intro _; simp only [wickKGChartOutput,if_neg inside]

end AASCKleinGordon
