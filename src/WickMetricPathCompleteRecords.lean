import WickAdmittedMetricPaths

/-! Complete records for the fixed KG branch after local admitted C1 path
queries are included. All old finite failures and inertial comparisons remain
questions. The comparison with the old record is a derived conservative
extension, not a source-identity certificate supplied by the user. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

inductive WickMetricPathRoleProtocol (Ω : Opens CoordinatePoint) where
  | original (question : WickRoleProtocol Ω)
  | path (act : WickAdmittedC1MetricPath Ω)

def wickMetricPathRoleOutput (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (u : WickNonzeroCore) : WickMetricPathRoleProtocol Ω → WickRoleReadout
  | .original π => wickUpstreamActionEvaluate (wickNativeActionRole a s Ω) u π
  | .path π => .metric (.first
      (wickAdmittedPathOutput a s (originalWickUnitRepresentative a u.val) π))

def wickMetricPathQuestionCompare {Ω : Opens CoordinatePoint} :
    WickMetricPathRoleProtocol Ω → WickRoleProtocol Ω
  | .original π => π
  | .path π => .metric (.first (wickKGIdentityAct π.analytic.tangentTest))

theorem wick_metric_path_entire_record_comparison (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u : WickNonzeroCore) (π : WickMetricPathRoleProtocol Ω) :
    wickMetricPathRoleOutput a s Ω u π =
      wickOriginalRoleOutput a s Ω u (wickMetricPathQuestionCompare π) := by
  cases π with
  | original π => exact wick_upstream_evaluation_entire_original a s Ω u π
  | path π =>
    exact congrArg (fun z => WickRoleReadout.metric (.first z))
      (wick_admitted_path_output_is_original_first a s (originalWickUnitRepresentative a u.val) π)

def wickMetricPathRoleSetoid (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    Setoid WickNonzeroCore where
  r u v := ∀ π,wickMetricPathRoleOutput a s Ω u π = wickMetricPathRoleOutput a s Ω v π
  iseqv := ⟨fun _ _ => rfl,fun h π => (h π).symm,fun h k π => (h π).trans (k π)⟩

theorem wick_metric_path_record_iff_original (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u v : WickNonzeroCore) :
    (wickMetricPathRoleSetoid a s Ω).r u v ↔ (wickOriginalRoleSetoid a s Ω).r u v := by
  constructor
  · intro same π
    have h := same (.original π)
    simpa only [wick_metric_path_entire_record_comparison,wickMetricPathQuestionCompare] using h
  · intro same π
    rw [wick_metric_path_entire_record_comparison,wick_metric_path_entire_record_comparison]
    exact same (wickMetricPathQuestionCompare π)

theorem wick_metric_path_record_iff_ray (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u v : WickNonzeroCore) :
    (wickMetricPathRoleSetoid a s Ω).r u v ↔ wickCoreRaySetoid.r u v :=
  (wick_metric_path_record_iff_original a s Ω u v).trans
    (wick_role_signature_iff_original_ray a s Ω u v)

abbrev WickMetricPathQresp (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :=
  Quotient (wickMetricPathRoleSetoid a s Ω)

def wickMetricPathResponseEquiv (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    WickMetricPathQresp a s Ω ≃ WickRoleQresp a s Ω where
  toFun := Quotient.map id (fun u v => (wick_metric_path_record_iff_original a s Ω u v).mp)
  invFun := Quotient.map id (fun u v => (wick_metric_path_record_iff_original a s Ω u v).mpr)
  left_inv q := by induction q using Quotient.inductionOn with | _ u => rfl
  right_inv q := by induction q using Quotient.inductionOn with | _ u => rfl

def wickMetricPathRoleEval (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    Quotient wickCoreRaySetoid → WickMetricPathQresp a s Ω :=
  Quotient.map id (fun u v => (wick_metric_path_record_iff_ray a s Ω u v).mpr)

theorem wick_metric_path_evaluation_comparison (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCoreRaySetoid) :
    wickMetricPathResponseEquiv a s Ω (wickMetricPathRoleEval a s Ω r) =
      wickCommonRoleEvaluation a s Ω r := by
  induction r using Quotient.inductionOn with | _ u => rfl

theorem wick_metric_path_finite_failure_retained (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u : WickNonzeroCore) (H : MetricSourceProbe Ω)
    (outside : H ∉ wickOriginalMetricNeighborhood Ω) :
    wickMetricPathRoleOutput a s Ω u (.original (.metric (.finite H))) = .metric .failed := by
  rw [wick_metric_path_entire_record_comparison]
  exact congrArg WickRoleReadout.metric
    (wick_KG_original_finite_failure a s (originalWickUnitRepresentative a u.val) H outside)

theorem wick_metric_path_comparison_retained (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u probe : WickNonzeroCore) (g : ProperPoincareTransform) :
    wickMetricPathRoleOutput a s Ω u (.original (.comparison g probe)) =
      .probability (wickOriginalRoleComparison a u probe g) := rfl

/-- The original strongly continuous, core-preserving representation is used
by the retained inertial restriction. No new inertial bridge is a premise. -/
theorem wick_metric_path_inertial_restriction (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u probe : WickNonzeroCore) (g : ProperPoincareTransform) :
    wickMetricPathRoleOutput a s Ω u (.original (.comparison g probe)) =
      .probability (‖inner ℂ
        (finiteParticleCoreToFock a (originalWickUnitRepresentative a probe.val))
        ((wickRoleInertialWitness a s Ω u).representation g
          (finiteParticleCoreToFock a (originalWickUnitRepresentative a u.val)))‖^2) :=
  (wickRoleInertialWitness a s Ω u).transport_restriction g probe

end AASCKleinGordon
