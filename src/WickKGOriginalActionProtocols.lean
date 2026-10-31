import WickOriginalFiniteActionDomain

/-! The source-declared KG finite-action presentation, with the A03 Gâteaux
readout grammar, fixed BEFORE the computed source. Finite requests retain their
admission/failure result. First acts are actual scalar reparameterizations of
every native direction; incidence is through their actual metric derivative.
This constructs the declared occupant, not a map from an arbitrary prior p. -/
noncomputable section
set_option maxHeartbeats 1000000
open Set Filter TopologicalSpace
open scoped Topology Matrix.Norms.Operator
open AASCSemanticExhaustion
namespace AASCKleinGordon

abbrev WickKGAdmittedFiniteMetric (Ω : Opens CoordinatePoint) :=
  {H : MetricSourceProbe Ω // H∈wickOriginalMetricNeighborhood Ω}

def wickKGFiniteActionCarrier (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    (Ω : Opens CoordinatePoint) (H : WickKGAdmittedFiniteMetric Ω) : ℝ :=
  wickOriginalRealFiniteAction a s u H.val

structure WickKGFirstMetricAct (Ω : Opens CoordinatePoint) where
  test : MetricSourceProbe Ω
  parameter : ℝ → ℝ
  rate : ℝ
  parameter_zero : parameter 0=0
  parameter_C1 : ContDiffAt ℝ 1 parameter 0
  derivative : HasDerivAt parameter rate 0

def wickKGFirstTangent {Ω : Opens CoordinatePoint} (δ : WickKGFirstMetricAct Ω) :
    MetricSourceProbe Ω := δ.rate • δ.test

def wickKGFirstMetricCurve {Ω : Opens CoordinatePoint} (δ : WickKGFirstMetricAct Ω)
    (t : ℝ) : Spacetime → NativeRealMatrix :=
  wickOriginalFiniteMetric (δ.parameter t • δ.test)

theorem wick_KG_original_act_admitted {Ω : Opens CoordinatePoint} (δ : WickKGFirstMetricAct Ω) :
    ∀ᶠ t in 𝓝 0,δ.parameter t • δ.test∈wickOriginalMetricNeighborhood Ω :=
  wick_original_reparameterized_direction_admitted Ω δ.test δ.parameter δ.parameter_zero
    δ.derivative.continuousAt

theorem wick_KG_original_act_tangent {Ω : Opens CoordinatePoint} (δ : WickKGFirstMetricAct Ω)
    (x : Spacetime) :
    HasDerivAt (fun t => wickKGFirstMetricCurve δ t x)
      (wickNativeMetricVariation (wickKGFirstTangent δ) x) 0 := by
  have h := (δ.derivative.smul_const (wickNativeMetricVariation δ.test x)).const_add wickFlatMetric
  simpa only [wickKGFirstMetricCurve,wickOriginalFiniteMetric,
    wick_native_metric_variation_smul,wickKGFirstTangent] using h

theorem wick_KG_original_act_base {Ω : Opens CoordinatePoint} (δ : WickKGFirstMetricAct Ω)
    (x : Spacetime) : wickKGFirstMetricCurve δ 0 x=wickFlatMetric := by
  change wickFlatMetric+wickNativeMetricVariation (δ.parameter 0 • δ.test) x=wickFlatMetric
  rw [wick_native_metric_variation_smul,δ.parameter_zero,zero_smul,add_zero]

def wickKGIdentityAct {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) :
    WickKGFirstMetricAct Ω where
  test := H
  parameter := id
  rate := 1
  parameter_zero := rfl
  parameter_C1 := contDiffAt_id
  derivative := hasDerivAt_id 0

theorem wick_KG_identity_tangent {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) :
    wickKGFirstTangent (wickKGIdentityAct H)=H := one_smul ℝ H

inductive WickKGOriginalProtocol (Ω : Opens CoordinatePoint) where
  | finite (request : MetricSourceProbe Ω)
  | first (act : WickKGFirstMetricAct Ω)

inductive WickKGOriginalReadout where
  | finite (value : ℝ)
  | first (value : ℝ)
  | failed

def wickKGFirstOutput (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    {Ω : Opens CoordinatePoint} (δ : WickKGFirstMetricAct Ω) : ℝ :=
  deriv (fun t => wickOriginalRealFiniteAction a s u (δ.parameter t • δ.test)) 0

def wickKGOriginalOutput (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    {Ω : Opens CoordinatePoint} : WickKGOriginalProtocol Ω → WickKGOriginalReadout := by
  classical
  exact fun
    | .finite H => if inside : H∈wickOriginalMetricNeighborhood Ω then
        .finite (wickKGFiniteActionCarrier a s u Ω ⟨H,inside⟩) else .failed
    | .first δ => .first (wickKGFirstOutput a s u δ)

def wickKGOriginalIncidence {Ω : Opens CoordinatePoint}
    (π : WickKGOriginalProtocol Ω) (δ : WickKGFirstMetricAct Ω) : Prop := π=.first δ

def wickKGOriginalMetInc {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω)
    (π : WickKGOriginalProtocol Ω) : Prop :=
  ∃ δ,wickKGOriginalIncidence π δ ∧ wickKGFirstTangent δ=H

def wickKGOriginalMetResp (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) (z : ℝ) : Prop :=
  ∃ π,wickKGOriginalMetInc H π ∧ wickKGOriginalOutput a s u π=.first z

theorem wick_real_derivative_value (f : ℝ → ℝ) (r : ℝ) (h : HasDerivAt f r 0) : deriv f 0=r := h.deriv

theorem wick_KG_original_first_output_computed (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    {Ω : Opens CoordinatePoint} (δ : WickKGFirstMetricAct Ω) :
    wickKGFirstOutput a s u δ=originalWickNativeRealMetricResponse a s u Ω (wickKGFirstTangent δ) := by
  have derivative := wick_original_finite_action_reparameterized a s u Ω δ.test δ.parameter δ.rate
    δ.parameter_zero δ.derivative
  have value := wick_real_derivative_value _ _ derivative
  exact value.trans (congrArg (fun H : MetricSourceProbe Ω => originalWickNativeRealMetricResponse a s u Ω H)
    (rfl : δ.rate • δ.test=wickKGFirstTangent δ))

theorem wick_KG_original_finite_failure (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω)
    (outside : H∉wickOriginalMetricNeighborhood Ω) :
    wickKGOriginalOutput a s u (.finite H)=.failed := by
  simp only [wickKGOriginalOutput,dif_neg outside]

theorem wick_KG_original_finite_success (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω)
    (inside : H∈wickOriginalMetricNeighborhood Ω) :
    wickKGOriginalOutput a s u (.finite H)=.finite (wickOriginalRealFiniteAction a s u H) := by
  simp only [wickKGOriginalOutput,dif_pos inside,wickKGFiniteActionCarrier]

theorem wick_KG_original_response_graph (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω) (z : ℝ) :
    wickKGOriginalMetResp a s u H z ↔ originalWickNativeRealMetricResponse a s u Ω H=z := by
  constructor
  · rintro ⟨π,⟨δ,incident,tangent⟩,output⟩
    change π=.first δ at incident
    subst π
    have hz : wickKGFirstOutput a s u δ=z := WickKGOriginalReadout.first.inj output
    exact (congrArg (originalWickNativeRealMetricResponse a s u Ω) tangent).symm.trans
      ((wick_KG_original_first_output_computed a s u δ).symm.trans hz)
  · intro hz
    refine ⟨.first (wickKGIdentityAct H),⟨wickKGIdentityAct H,rfl,wick_KG_identity_tangent H⟩,?_⟩
    apply congrArg WickKGOriginalReadout.first
    exact (wick_KG_original_first_output_computed a s u (wickKGIdentityAct H)).trans
      ((congrArg (originalWickNativeRealMetricResponse a s u Ω) (wick_KG_identity_tangent H)).trans hz)

theorem wick_KG_original_tangent_coherence (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    {Ω : Opens CoordinatePoint} (δ ε : WickKGFirstMetricAct Ω)
    (same : wickKGFirstTangent δ=wickKGFirstTangent ε) :
    wickKGFirstOutput a s u δ=wickKGFirstOutput a s u ε :=
  (wick_KG_original_first_output_computed a s u δ).trans
    ((congrArg (originalWickNativeRealMetricResponse a s u Ω) same).trans
      (wick_KG_original_first_output_computed a s u ε).symm)

end AASCKleinGordon
