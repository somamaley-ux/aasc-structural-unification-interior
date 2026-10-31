import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Tactic

/-! Module A 3.6--3.11, in an actual coordinate LF test space.
The incidence and output are fixed before the response is constructed.
Native tangent/protocol provenance, naturality and completeness are separate
attachment obligations; this file does not infer them from Kernel necessity. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
open TopologicalSpace

abbrev MetricSourceProbe (Ω : Opens (Fin 4 → ℝ)) :=
  TestFunction Ω (Fin 10 → ℝ) (⊤ : ℕ∞)

structure OperationalMetricIncidence (Ω : Opens (Fin 4 → ℝ)) (Protocol : Type*) where
  incident : MetricSourceProbe Ω → Protocol → Prop
  output : Protocol → ℝ
  total : ∀ h, ∃ π, incident h π
  coherent : ∀ h π ρ, incident h π → incident h ρ → output π = output ρ
  add_compatible : ∀ h k π ρ, incident h π → incident k ρ →
    ∃ σ, incident (h + k) σ ∧ output σ = output π + output ρ
  smul_compatible : ∀ (r : ℝ) h π, incident h π →
    ∃ σ, incident (r • h) σ ∧ output σ = r * output π

variable {Ω : Opens (Fin 4 → ℝ)} {Protocol : Type*}

def operationalMetricResponse (d : OperationalMetricIncidence Ω Protocol)
    (h : MetricSourceProbe Ω) : ℝ := d.output (d.total h).choose

theorem operational_response_of_incident (d : OperationalMetricIncidence Ω Protocol)
    (h : MetricSourceProbe Ω) (π : Protocol) (hπ : d.incident h π) :
    operationalMetricResponse d h = d.output π :=
  d.coherent h _ π (d.total h).choose_spec hπ

theorem operational_response_graph (d : OperationalMetricIncidence Ω Protocol)
    (h : MetricSourceProbe Ω) (a : ℝ) :
    operationalMetricResponse d h = a ↔ ∃ π, d.incident h π ∧ d.output π = a := by
  constructor
  · intro ha
    exact ⟨(d.total h).choose, (d.total h).choose_spec, ha⟩
  · rintro ⟨π, hπ, ha⟩
    exact (operational_response_of_incident d h π hπ).trans ha

theorem operational_response_add (d : OperationalMetricIncidence Ω Protocol)
    (h k : MetricSourceProbe Ω) :
    operationalMetricResponse d (h + k) =
      operationalMetricResponse d h + operationalMetricResponse d k := by
  obtain ⟨σ, hσ, out⟩ := d.add_compatible h k _ _ (d.total h).choose_spec (d.total k).choose_spec
  exact (operational_response_of_incident d (h + k) σ hσ).trans out

theorem operational_response_smul (d : OperationalMetricIncidence Ω Protocol)
    (r : ℝ) (h : MetricSourceProbe Ω) :
    operationalMetricResponse d (r • h) = r • operationalMetricResponse d h := by
  obtain ⟨σ, hσ, out⟩ := d.smul_compatible r h _ (d.total h).choose_spec
  exact (operational_response_of_incident d (r • h) σ hσ).trans out

/-- LF continuity is checked on every fixed-compact piece, as in the source.
No norm topology is substituted for the compact-test LF topology. -/
def operationalMetricFunctional (d : OperationalMetricIncidence Ω Protocol)
    (continuous_on_compacts : ∀ (K : Compacts (Fin 4 → ℝ))
      (hK : (K : Set (Fin 4 → ℝ)) ⊆ Ω),
      Continuous (operationalMetricResponse d ∘ TestFunction.ofSupportedIn hK)) :
    MetricSourceProbe Ω →L[ℝ] ℝ :=
  TestFunction.mkCLM ℝ (operationalMetricResponse d)
    (operational_response_add d) (operational_response_smul d) continuous_on_compacts

theorem operational_metric_functional_exists_unique
    (d : OperationalMetricIncidence Ω Protocol)
    (continuous_on_compacts : ∀ (K : Compacts (Fin 4 → ℝ))
      (hK : (K : Set (Fin 4 → ℝ)) ⊆ Ω),
      Continuous (operationalMetricResponse d ∘ TestFunction.ofSupportedIn hK)) :
    ∃! W : MetricSourceProbe Ω →L[ℝ] ℝ,
      ∀ h a, W h = a ↔ ∃ π, d.incident h π ∧ d.output π = a := by
  refine ⟨operationalMetricFunctional d continuous_on_compacts, ?_, ?_⟩
  · exact operational_response_graph d
  · intro W hW
    ext h
    apply (hW h _).mpr
    exact ⟨(d.total h).choose, (d.total h).choose_spec, rfl⟩

theorem operational_metric_zero_iff (d : OperationalMetricIncidence Ω Protocol) :
    (∀ h, operationalMetricResponse d h = 0) ↔
      ∀ h π, d.incident h π → d.output π = 0 := by
  constructor
  · intro hz h π hπ
    exact (operational_response_of_incident d h π hπ).symm.trans (hz h)
  · intro hz h
    exact hz h _ (d.total h).choose_spec

/-- Failure tests refer to the independently fixed incidence/output relation. -/
theorem no_operational_attachment_of_missing_probe
    (incident : MetricSourceProbe Ω → Protocol → Prop) (output : Protocol → ℝ)
    (h : MetricSourceProbe Ω) (missing : ¬ ∃ π, incident h π) :
    ¬ ∃ W : MetricSourceProbe Ω →L[ℝ] ℝ,
      ∀ k a, W k = a ↔ ∃ π, incident k π ∧ output π = a := by
  rintro ⟨W, graph⟩
  obtain ⟨π, hπ, _⟩ := (graph h (W h)).mp rfl
  exact missing ⟨π, hπ⟩

#print axioms operational_response_of_incident
#print axioms operational_response_graph
#print axioms operational_response_add
#print axioms operational_response_smul
#print axioms operational_metric_functional_exists_unique
#print axioms operational_metric_zero_iff
#print axioms no_operational_attachment_of_missing_probe
end
end AASCSemanticExhaustion
