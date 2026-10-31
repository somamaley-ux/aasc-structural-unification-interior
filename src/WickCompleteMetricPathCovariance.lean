import WickChartAdmittedPathTransport

/-! Full question covariance, with finite admission/failure evaluated in the
transported chart. The original program and all added admitted C1 paths are
retained. Outputs are actual finite action, derivatives and Born comparisons. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

inductive WickChartMetricPathProtocol (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) where
  | original (question : WickRoleProtocol Ω)
  | path (act : WickChartAdmittedMetricPath Ω D)

def wickChartOriginalRoleOutput (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (u : WickNonzeroCore) : WickRoleProtocol Ω → WickRoleReadout := by
  classical
  exact fun
    | .metric (.finite H) => if H∈D then
        .metric (.finite (wickOriginalRealFiniteAction a s (originalWickUnitRepresentative a u.val) H))
        else .metric .failed
    | .metric (.first δ) => .metric (.first
        (wickKGFirstOutput a s (originalWickUnitRepresentative a u.val) δ))
    | .comparison g v => .probability (wickOriginalRoleComparison a u v g)

def wickChartMetricPathOutput (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (u : WickNonzeroCore) :
    WickChartMetricPathProtocol Ω D → WickRoleReadout
  | .original π => wickChartOriginalRoleOutput a s Ω D u π
  | .path π => .metric (.first (wickChartPathOutput a s (originalWickUnitRepresentative a u.val) π))

def wickOriginalMetricPathInChart {Ω : Opens CoordinatePoint} :
    WickMetricPathRoleProtocol Ω →
      WickChartMetricPathProtocol Ω (wickOriginalMetricNeighborhood Ω)
  | .original π => .original π
  | .path π => .path (wickOriginalChartPath π)

theorem wick_original_metric_path_chart_exact (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u : WickNonzeroCore) (π : WickMetricPathRoleProtocol Ω) :
    wickChartMetricPathOutput a s Ω (wickOriginalMetricNeighborhood Ω) u
      (wickOriginalMetricPathInChart π) = wickMetricPathRoleOutput a s Ω u π := by
  cases π with
  | path π => rfl
  | original π =>
    cases π with
    | comparison g v => rfl
    | metric π =>
      cases π with
      | first δ => rfl
      | finite H =>
        by_cases inside : H∈wickOriginalMetricNeighborhood Ω
        · simp only [wickOriginalMetricPathInChart,wickChartMetricPathOutput,wickChartOriginalRoleOutput,
            wickMetricPathRoleOutput,wickUpstreamActionEvaluate,wickNativeActionRole,if_pos inside]
        · simp only [wickOriginalMetricPathInChart,wickChartMetricPathOutput,wickChartOriginalRoleOutput,
            wickMetricPathRoleOutput,wickUpstreamActionEvaluate,wickNativeActionRole,if_neg inside]

def wickChartMetricPathProtocolPoincare (a : Parameters) (q : ProperPoincareTransform)
    {Ω : Opens CoordinatePoint} {D : Set (MetricSourceProbe Ω)} :
    WickChartMetricPathProtocol Ω D →
      WickChartMetricPathProtocol (wickAffineMetricRegion q.left.toAdd q.right Ω)
        (wickNativeAffineMetricTest q.left.toAdd q.right '' D)
  | .original π => .original (wickCovariantRoleProtocolTransport a q π)
  | .path π => .path (wickChartPathPoincare q.left.toAdd q.right π)

theorem wick_chart_metric_domain_exact (b : Spacetime) (L : ProperLorentzTransform)
    {Ω : Opens CoordinatePoint} (D : Set (MetricSourceProbe Ω)) (H : MetricSourceProbe Ω) :
    wickNativeAffineMetricTest b L H ∈ wickNativeAffineMetricTest b L '' D ↔ H∈D := by
  constructor
  · rintro ⟨K,inside,same⟩
    exact (wick_native_affine_test_injective b L Ω same) ▸ inside
  · intro inside
    exact ⟨H,inside,rfl⟩

theorem wick_chart_original_output_poincare (a : Parameters) (s : ℝ)
    (q : ProperPoincareTransform) (Ω : Opens CoordinatePoint) (D : Set (MetricSourceProbe Ω))
    (u : WickNonzeroCore) (π : WickRoleProtocol Ω) :
    wickChartOriginalRoleOutput a s (wickAffineMetricRegion q.left.toAdd q.right Ω)
      (wickNativeAffineMetricTest q.left.toAdd q.right '' D)
      (wickPoincareNonzeroCore a q.left.toAdd q.right u)
      (wickCovariantRoleProtocolTransport a q π) = wickChartOriginalRoleOutput a s Ω D u π := by
  classical
  cases π with
  | comparison g v =>
    exact congrArg WickRoleReadout.probability
      (wick_original_role_comparison_poincare a q g u v)
  | metric π =>
    cases π with
    | first δ =>
      change WickRoleReadout.metric (.first
        (wickKGFirstOutput a s (originalWickUnitRepresentative a (corePoincare a q.left.toAdd q.right u.val))
          (wickKGFirstActPoincare q.left.toAdd q.right δ))) = _
      rw [wick_unit_representative_poincare,wick_KG_first_output_poincare]
      rfl
    | finite H =>
      have exactDomain := wick_chart_metric_domain_exact q.left.toAdd q.right D H
      by_cases inside : H∈D
      · have pushed := exactDomain.mpr inside
        simp only [wickChartOriginalRoleOutput,wickCovariantRoleProtocolTransport,
          wickKGProtocolPoincare,if_pos inside,if_pos pushed]
        change WickRoleReadout.metric (.finite
          (wickOriginalRealFiniteAction a s
            (originalWickUnitRepresentative a (corePoincare a q.left.toAdd q.right u.val))
            (wickNativeAffineMetricTest q.left.toAdd q.right H))) = _
        rw [wick_unit_representative_poincare,wick_original_real_finite_action_poincare]
      · have rejected : wickNativeAffineMetricTest q.left.toAdd q.right H ∉
            wickNativeAffineMetricTest q.left.toAdd q.right '' D := fun h => inside (exactDomain.mp h)
        simp only [wickChartOriginalRoleOutput,wickCovariantRoleProtocolTransport,
          wickKGProtocolPoincare,if_neg inside,if_neg rejected]

theorem wick_complete_metric_path_output_poincare (a : Parameters) (s : ℝ)
    (q : ProperPoincareTransform) (Ω : Opens CoordinatePoint) (D : Set (MetricSourceProbe Ω))
    (u : WickNonzeroCore) (π : WickChartMetricPathProtocol Ω D) :
    wickChartMetricPathOutput a s (wickAffineMetricRegion q.left.toAdd q.right Ω)
      (wickNativeAffineMetricTest q.left.toAdd q.right '' D)
      (wickPoincareNonzeroCore a q.left.toAdd q.right u)
      (wickChartMetricPathProtocolPoincare a q π) = wickChartMetricPathOutput a s Ω D u π := by
  cases π with
  | original π => exact wick_chart_original_output_poincare a s q Ω D u π
  | path π =>
    change WickRoleReadout.metric (.first (wickChartPathOutput a s
      (originalWickUnitRepresentative a (corePoincare a q.left.toAdd q.right u.val))
      (wickChartPathPoincare q.left.toAdd q.right π))) = _
    rw [wick_unit_representative_poincare,wick_chart_path_output_poincare]
    rfl

theorem wick_chart_normalized_finite_action_same_ray (a : Parameters) (s : ℝ)
    (u v : WickNonzeroCore) (same : wickCoreRaySetoid.r u v)
    {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) :
    wickOriginalRealFiniteAction a s (originalWickUnitRepresentative a u.val) H =
      wickOriginalRealFiniteAction a s (originalWickUnitRepresentative a v.val) H := by
  obtain ⟨z,hz,phase⟩ := wick_role_normalized_phase a u v same
  rw [phase]
  exact (congrArg Complex.re (wick_original_finite_action_unit_phase a s z hz
    (originalWickUnitRepresentative a u.val) (originalWickUnitRepresentative a u.val) H)).symm

theorem wick_chart_original_output_same_ray (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (D : Set (MetricSourceProbe Ω)) (u v : WickNonzeroCore)
    (same : wickCoreRaySetoid.r u v) (π : WickRoleProtocol Ω) :
    wickChartOriginalRoleOutput a s Ω D u π = wickChartOriginalRoleOutput a s Ω D v π := by
  classical
  cases π with
  | comparison g probe =>
    exact congrArg WickRoleReadout.probability
      (wick_role_comparison_phase_invariant a u v same g probe)
  | metric π =>
    cases π with
    | first δ =>
      have functions := funext (fun t => wick_chart_normalized_finite_action_same_ray a s u v same
        (δ.parameter t • δ.test))
      exact congrArg (fun f : ℝ → ℝ => WickRoleReadout.metric (.first (deriv f 0))) functions
    | finite H =>
      by_cases inside : H∈D
      · simp only [wickChartOriginalRoleOutput,if_pos inside]
        exact congrArg (fun z => WickRoleReadout.metric (.finite z))
          (wick_chart_normalized_finite_action_same_ray a s u v same H)
      · simp only [wickChartOriginalRoleOutput,if_neg inside]

theorem wick_chart_metric_path_output_same_ray (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (D : Set (MetricSourceProbe Ω)) (u v : WickNonzeroCore)
    (same : wickCoreRaySetoid.r u v) (π : WickChartMetricPathProtocol Ω D) :
    wickChartMetricPathOutput a s Ω D u π = wickChartMetricPathOutput a s Ω D v π := by
  cases π with
  | original π => exact wick_chart_original_output_same_ray a s Ω D u v same π
  | path π =>
    have functions := funext (fun t => wick_chart_normalized_finite_action_same_ray a s u v same (π.lift t))
    exact congrArg (fun f : ℝ → ℝ => WickRoleReadout.metric (.first (deriv f 0))) functions

def wickChartMetricPathRayOutput (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) : Quotient wickCoreRaySetoid →
      WickChartMetricPathProtocol Ω D → WickRoleReadout :=
  Quotient.lift (wickChartMetricPathOutput a s Ω D) (by
    intro u v same
    funext π
    exact wick_chart_metric_path_output_same_ray a s Ω D u v same π)

theorem wick_complete_metric_path_ray_poincare (a : Parameters) (s : ℝ)
    (q : ProperPoincareTransform) (Ω : Opens CoordinatePoint) (D : Set (MetricSourceProbe Ω))
    (r : Quotient wickCoreRaySetoid) (π : WickChartMetricPathProtocol Ω D) :
    wickChartMetricPathRayOutput a s (wickAffineMetricRegion q.left.toAdd q.right Ω)
      (wickNativeAffineMetricTest q.left.toAdd q.right '' D)
      (wickPoincareRayAction a q.left.toAdd q.right r)
      (wickChartMetricPathProtocolPoincare a q π) = wickChartMetricPathRayOutput a s Ω D r π := by
  induction r using Quotient.inductionOn with | _ u =>
    exact wick_complete_metric_path_output_poincare a s q Ω D u π

end AASCKleinGordon
