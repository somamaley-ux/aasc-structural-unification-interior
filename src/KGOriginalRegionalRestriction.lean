import KGQuantumOrbitDescent

/-! Regional restriction is contravariant on records: a compact test supported
in the smaller open region is the same global test in the larger region.
Actual analytic path data, admission and finite rejection are retained. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open AASCSemanticExhaustion TopologicalSpace Set Filter

def kgExtendMetricProbe {Ω V : Opens CoordinatePoint} (h : Ω ≤ V)
    (H : MetricSourceProbe Ω) : MetricSourceProbe V :=
  ⟨H,H.contDiff,H.hasCompactSupport,fun _ hx => h (H.tsupport_subset hx)⟩

@[simp] theorem kg_extend_metric_probe_apply {Ω V : Opens CoordinatePoint}
    (h : Ω ≤ V) (H : MetricSourceProbe Ω) (x : CoordinatePoint) :
    kgExtendMetricProbe h H x=H x := rfl

def kgExtendMetricProbeLM {Ω V : Opens CoordinatePoint} (h : Ω ≤ V) :
    MetricSourceProbe Ω →ₗ[ℝ] MetricSourceProbe V where
  toFun := kgExtendMetricProbe h
  map_add' _ _ := by ext x;rfl
  map_smul' _ _ := by ext x;rfl

def kgExtendMetricProbeCLM {Ω V : Opens CoordinatePoint} (h : Ω ≤ V) :
    MetricSourceProbe Ω →L[ℝ] MetricSourceProbe V :=
  TestFunction.mkCLM ℝ (kgExtendMetricProbe h)
    (kgExtendMetricProbeLM h).map_add (kgExtendMetricProbeLM h).map_smul
    (fun K inside => by
      change Continuous (TestFunction.ofSupportedIn (inside.trans h))
      exact TestFunction.continuous_ofSupportedIn (inside.trans h))

theorem kg_extend_metric_admission {Ω V : Opens CoordinatePoint} (h : Ω ≤ V)
    (H : MetricSourceProbe Ω) :
    kgExtendMetricProbe h H ∈ wickOriginalMetricNeighborhood V ↔
      H ∈ wickOriginalMetricNeighborhood Ω := by
  have entries : ∀ i j,wickNativeBoundedEntry V i j (kgExtendMetricProbe h H)=
      wickNativeBoundedEntry Ω i j H := fun _ _ => by ext x;rfl
  simp only [wickOriginalMetricNeighborhood,mem_setOf_eq,entries]

def kgExtendFirstAct {Ω V : Opens CoordinatePoint} (h : Ω ≤ V)
    (δ : WickKGFirstMetricAct Ω) : WickKGFirstMetricAct V :=
  { δ with test := kgExtendMetricProbe h δ.test }

def kgExtendAnalyticPath {Ω V : Opens CoordinatePoint} (h : Ω ≤ V)
    (π : WickCompactC1MetricCurve Ω) : WickCompactC1MetricCurve V :=
  { π with tangentTest := kgExtendMetricProbe h π.tangentTest }

def kgExtendAdmittedPath {Ω V : Opens CoordinatePoint} (h : Ω ≤ V)
    (π : WickAdmittedC1MetricPath Ω) : WickAdmittedC1MetricPath V where
  analytic := kgExtendAnalyticPath h π.analytic
  lift t := kgExtendMetricProbe h (π.lift t)
  local_admitted := π.local_admitted.mono (fun _ ht => (kg_extend_metric_admission h _).mpr ht)
  local_projection := π.local_projection

def kgExtendMetricProtocol {Ω V : Opens CoordinatePoint} (h : Ω ≤ V) :
    WickKGOriginalProtocol Ω → WickKGOriginalProtocol V
  | .finite H => .finite (kgExtendMetricProbe h H)
  | .first δ => .first (kgExtendFirstAct h δ)

def kgExtendRoleProtocol {Ω V : Opens CoordinatePoint} (h : Ω ≤ V) :
    WickRoleProtocol Ω → WickRoleProtocol V
  | .metric π => .metric (kgExtendMetricProtocol h π)
  | .comparison g v => .comparison g v

def kgExtendOriginalProtocol {Ω V : Opens CoordinatePoint} (h : Ω ≤ V) :
    WickMetricPathRoleProtocol Ω → WickMetricPathRoleProtocol V
  | .original π => .original (kgExtendRoleProtocol h π)
  | .path π => .path (kgExtendAdmittedPath h π)

theorem kg_original_metric_regional_output (a : Parameters) (s : ℝ)
    {Ω V : Opens CoordinatePoint} (h : Ω ≤ V) (u : FiniteParticleCore)
    (π : WickKGOriginalProtocol Ω) :
    wickKGOriginalOutput a s u (kgExtendMetricProtocol h π)=wickKGOriginalOutput a s u π := by
  classical
  cases π with
  | finite H =>
    simp only [kgExtendMetricProtocol,wickKGOriginalOutput]
    by_cases inside : H ∈ wickOriginalMetricNeighborhood Ω
    · rw [dif_pos inside,dif_pos ((kg_extend_metric_admission h H).mpr inside)]
      rfl
    · rw [dif_neg inside,dif_neg (fun hv => inside ((kg_extend_metric_admission h H).mp hv))]
  | first δ => rfl

theorem kg_original_role_regional_output (a : Parameters) (s : ℝ)
    {Ω V : Opens CoordinatePoint} (h : Ω ≤ V) (u : WickNonzeroCore)
    (π : WickRoleProtocol Ω) :
    wickOriginalRoleOutput a s V u (kgExtendRoleProtocol h π)=
      wickOriginalRoleOutput a s Ω u π := by
  cases π with
  | metric π =>
    exact congrArg WickRoleReadout.metric
      (kg_original_metric_regional_output a s h (originalWickUnitRepresentative a u.val) π)
  | comparison g v => rfl

theorem kg_complete_original_regional_output (a : Parameters) (s : ℝ)
    {Ω V : Opens CoordinatePoint} (h : Ω ≤ V) (u : WickNonzeroCore)
    (π : WickMetricPathRoleProtocol Ω) :
    wickMetricPathRoleOutput a s V u (kgExtendOriginalProtocol h π)=
      wickMetricPathRoleOutput a s Ω u π := by
  cases π with
  | original π =>
    rw [wick_metric_path_entire_record_comparison,wick_metric_path_entire_record_comparison]
    exact kg_original_role_regional_output a s h u π
  | path π => rfl

theorem kg_regional_first_tangent {Ω V : Opens CoordinatePoint} (h : Ω ≤ V)
    (δ : WickKGFirstMetricAct Ω) :
    wickKGFirstTangent (kgExtendFirstAct h δ)=kgExtendMetricProbe h (wickKGFirstTangent δ) := by
  ext x;rfl

theorem kg_regional_path_curve {Ω V : Opens CoordinatePoint} (h : Ω ≤ V)
    (π : WickAdmittedC1MetricPath Ω) :
    (kgExtendAdmittedPath h π).analytic.curve=π.analytic.curve := rfl

theorem kg_regional_path_lift {Ω V : Opens CoordinatePoint} (h : Ω ≤ V)
    (π : WickAdmittedC1MetricPath Ω) (t : ℝ) :
    (kgExtendAdmittedPath h π).lift t=kgExtendMetricProbe h (π.lift t) := rfl

theorem kg_regional_protocol_identity (Ω : Opens CoordinatePoint)
    (π : WickMetricPathRoleProtocol Ω) : kgExtendOriginalProtocol (le_refl Ω) π=π := by
  cases π with
  | original π => cases π with
    | metric π => cases π <;> rfl
    | comparison g v => rfl
  | path π => cases π; rfl

theorem kg_regional_protocol_comp {Ω V W : Opens CoordinatePoint}
    (h : Ω ≤ V) (k : V ≤ W) (π : WickMetricPathRoleProtocol Ω) :
    kgExtendOriginalProtocol k (kgExtendOriginalProtocol h π)=
      kgExtendOriginalProtocol (h.trans k) π := by
  cases π with
  | original π => cases π with
    | metric π => cases π <;> rfl
    | comparison g v => rfl
  | path π => cases π; rfl

end AASCKleinGordon
