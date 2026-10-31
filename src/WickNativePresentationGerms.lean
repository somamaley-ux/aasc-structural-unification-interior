import WickNativeDeclaredSourcePresentation

noncomputable section
open TopologicalSpace Filter
open scoped Topology
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem wick_declared_presentation_every_first_germ_admitted (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) (D : Set (MetricSourceProbe Ω))
    (p : WickNativeDeclaredSourcePresentation a s u Ω D) (δ : WickKGFirstMetricAct Ω) :
    ∀ᶠ t in 𝓝 0,δ.parameter t • δ.test∈D := by
  have continuous : ContinuousAt (fun t : ℝ => δ.parameter t • δ.test) 0 :=
    δ.derivative.continuousAt.smul continuousAt_const
  have base : δ.parameter 0 • δ.test∈D := by
    rw [δ.parameter_zero,zero_smul]
    exact p.domain_zero
  exact continuous (p.domain_open.mem_nhds base)

theorem wick_declared_presentation_first_germ_metrics_admissible (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) (D : Set (MetricSourceProbe Ω))
    (p : WickNativeDeclaredSourcePresentation a s u Ω D) (δ : WickKGFirstMetricAct Ω) :
    ∀ᶠ t in 𝓝 0,∀ x,WickIntrinsicLorentzSignature (wickKGFirstMetricCurve δ t x) ∧
      (wickKGFirstMetricCurve δ t x).det≠0 :=
  (wick_declared_presentation_every_first_germ_admitted a s u Ω D p δ).mono
    (fun t inside => p.metric_admissible _ inside)

end AASCKleinGordon
