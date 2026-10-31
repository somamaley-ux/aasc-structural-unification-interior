import WickCompleteMetricPathCovariance

/-! Actual tangent incidence, whole-receiver graph naturality, and the
commuting law with the frozen ORIGINAL source-base identification. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickChartMetricQuestion {Ω : Opens CoordinatePoint} {D : Set (MetricSourceProbe Ω)} :
    WickChartMetricPathProtocol Ω D → WickRoleProtocol Ω
  | .original π => π
  | .path π => .metric (.first (wickKGIdentityAct π.analytic.tangentTest))

def wickRoleQuestionMetInc {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω)
    (π : WickRoleProtocol Ω) : Prop :=
  ∃ δ,π = .metric (.first δ) ∧ wickKGFirstTangent δ = H

def wickChartMetricPathMetInc {Ω : Opens CoordinatePoint} {D : Set (MetricSourceProbe Ω)}
    (H : MetricSourceProbe Ω) (π : WickChartMetricPathProtocol Ω D) : Prop :=
  wickRoleQuestionMetInc H (wickChartMetricQuestion π)

theorem wick_chart_metric_question_poincare (a : Parameters) (q : ProperPoincareTransform)
    {Ω : Opens CoordinatePoint} {D : Set (MetricSourceProbe Ω)} (π : WickChartMetricPathProtocol Ω D) :
    wickChartMetricQuestion (wickChartMetricPathProtocolPoincare a q π) =
      wickCovariantRoleProtocolTransport a q (wickChartMetricQuestion π) := by
  cases π <;> rfl

theorem wick_role_question_metric_incidence {Ω : Opens CoordinatePoint}
    (H : MetricSourceProbe Ω) (π : WickKGOriginalProtocol Ω) :
    wickRoleQuestionMetInc H (.metric π) ↔ wickKGOriginalMetInc H π := by
  simp only [wickRoleQuestionMetInc,wickKGOriginalMetInc,wickKGOriginalIncidence,
    WickRoleProtocol.metric.injEq]

theorem wick_role_question_incidence_poincare (a : Parameters) (q : ProperPoincareTransform)
    {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) (π : WickRoleProtocol Ω) :
    wickRoleQuestionMetInc (wickNativeAffineMetricTest q.left.toAdd q.right H)
      (wickCovariantRoleProtocolTransport a q π) ↔ wickRoleQuestionMetInc H π := by
  cases π with
  | comparison g v => simp [wickRoleQuestionMetInc,wickCovariantRoleProtocolTransport]
  | metric π =>
    change wickRoleQuestionMetInc _ (.metric (wickKGProtocolPoincare q.left.toAdd q.right π)) ↔ _
    rw [wick_role_question_metric_incidence,wick_role_question_metric_incidence]
    exact wick_KG_incidence_poincare q.left.toAdd q.right Ω H π

theorem wick_chart_metric_incidence_poincare (a : Parameters) (q : ProperPoincareTransform)
    {Ω : Opens CoordinatePoint} {D : Set (MetricSourceProbe Ω)} (H : MetricSourceProbe Ω)
    (π : WickChartMetricPathProtocol Ω D) :
    wickChartMetricPathMetInc (wickNativeAffineMetricTest q.left.toAdd q.right H)
      (wickChartMetricPathProtocolPoincare a q π) ↔ wickChartMetricPathMetInc H π := by
  unfold wickChartMetricPathMetInc
  rw [wick_chart_metric_question_poincare]
  exact wick_role_question_incidence_poincare a q H (wickChartMetricQuestion π)

theorem wick_chart_first_response_collapse (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (D : Set (MetricSourceProbe Ω)) (u : WickNonzeroCore)
    (π : WickChartMetricPathProtocol Ω D) :
    wickChartMetricPathOutput a s Ω D u π =
      wickChartOriginalRoleOutput a s Ω D u (wickChartMetricQuestion π) := by
  cases π with
  | original π => rfl
  | path π =>
    change WickRoleReadout.metric (.first (wickChartPathOutput a s
      (originalWickUnitRepresentative a u.val) π)) =
      .metric (.first (wickKGFirstOutput a s (originalWickUnitRepresentative a u.val)
        (wickKGIdentityAct π.analytic.tangentTest)))
    rw [wick_chart_path_output_computed,wick_KG_original_first_output_computed,wick_KG_identity_tangent]

def wickChartMetricPathMetResp (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (u : WickNonzeroCore) (H : MetricSourceProbe Ω) (z : ℝ) : Prop :=
  ∃ π,wickChartMetricPathMetInc H π ∧ wickChartMetricPathOutput a s Ω D u π = .metric (.first z)

theorem wick_complete_chart_metric_response_graph (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (D : Set (MetricSourceProbe Ω)) (u : WickNonzeroCore)
    (H : MetricSourceProbe Ω) (z : ℝ) :
    wickChartMetricPathMetResp a s Ω D u H z ↔
      originalWickNativeRealMetricResponse a s (originalWickUnitRepresentative a u.val) Ω H = z := by
  constructor
  · rintro ⟨π,⟨δ,incident,tangent⟩,output⟩
    rw [wick_chart_first_response_collapse,incident] at output
    have first : wickKGFirstOutput a s (originalWickUnitRepresentative a u.val) δ = z :=
      WickKGOriginalReadout.first.inj (WickRoleReadout.metric.inj output)
    exact (congrArg (originalWickNativeRealMetricResponse a s
      (originalWickUnitRepresentative a u.val) Ω) tangent).symm.trans
      ((wick_KG_original_first_output_computed a s
        (originalWickUnitRepresentative a u.val) δ).symm.trans first)
  · intro hz
    refine ⟨.original (.metric (.first (wickKGIdentityAct H))),
      ⟨wickKGIdentityAct H,rfl,wick_KG_identity_tangent H⟩,?_⟩
    change WickRoleReadout.metric (.first (wickKGFirstOutput a s
      (originalWickUnitRepresentative a u.val) (wickKGIdentityAct H))) = _
    rw [wick_KG_original_first_output_computed,wick_KG_identity_tangent,hz]

/-- The whole target receiver is used, not only a convenient image subset. -/
theorem wick_complete_chart_metric_graph_poincare (a : Parameters) (s : ℝ)
    (q : ProperPoincareTransform) (Ω : Opens CoordinatePoint) (D : Set (MetricSourceProbe Ω))
    (u : WickNonzeroCore) (H : MetricSourceProbe Ω) (z : ℝ) :
    wickChartMetricPathMetResp a s (wickAffineMetricRegion q.left.toAdd q.right Ω)
      (wickNativeAffineMetricTest q.left.toAdd q.right '' D)
      (wickPoincareNonzeroCore a q.left.toAdd q.right u)
      (wickNativeAffineMetricTest q.left.toAdd q.right H) z ↔
      wickChartMetricPathMetResp a s Ω D u H z := by
  have normalization :
      originalWickUnitRepresentative a (wickPoincareNonzeroCore a q.left.toAdd q.right u).val =
        corePoincare a q.left.toAdd q.right (originalWickUnitRepresentative a u.val) :=
    wick_unit_representative_poincare a q.left.toAdd q.right u.val
  have response := (congrArg (fun v : FiniteParticleCore =>
      originalWickNativeRealMetricResponse a s v (wickAffineMetricRegion q.left.toAdd q.right Ω)
        (wickNativeAffineMetricTest q.left.toAdd q.right H)) normalization).trans
    (wick_original_native_response_poincare a q.left.toAdd q.right s
      (originalWickUnitRepresentative a u.val) Ω H)
  exact (wick_complete_chart_metric_response_graph a s (wickAffineMetricRegion q.left.toAdd q.right Ω)
    (wickNativeAffineMetricTest q.left.toAdd q.right '' D)
    (wickPoincareNonzeroCore a q.left.toAdd q.right u)
    (wickNativeAffineMetricTest q.left.toAdd q.right H) z).trans
    ((Iff.intro (fun h => response.symm.trans h) (fun h => response.trans h)).trans
      (wick_complete_chart_metric_response_graph a s Ω D u H z).symm)

def wickIdentifiedMetricPathRecordReadout (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    WickMetricPathQresp a s Ω → WickMetricPathRoleProtocol Ω → WickRoleReadout :=
  Quotient.lift (wickMetricPathRoleOutput a s Ω) (by
    intro u v same
    funext π
    exact same π)

theorem wick_original_chart_readout_is_identified_source (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCoreRaySetoid) (π : WickMetricPathRoleProtocol Ω) :
    wickChartMetricPathRayOutput a s Ω (wickOriginalMetricNeighborhood Ω) r
      (wickOriginalMetricPathInChart π) =
      wickIdentifiedMetricPathRecordReadout a s Ω
        (wickMetricPathF a s Ω (wickMetricPathPiA a s Ω
          (wickCommonRoleSourcePresentation a s Ω r))).val π := by
  rw [wick_metric_path_original_source_identification]
  induction r using Quotient.inductionOn with | _ u =>
    exact wick_original_metric_path_chart_exact a s Ω u π

/-- B Definition4.1(5)'s added-path operational covariance, retaining the full
frozen original record on the right and the transported finite chart on the left. -/
theorem wick_metric_path_covariant_original_source_square (a : Parameters) (s : ℝ)
    (q : ProperPoincareTransform) (Ω : Opens CoordinatePoint)
    (r : Quotient wickCoreRaySetoid) (π : WickMetricPathRoleProtocol Ω) :
    wickChartMetricPathRayOutput a s (wickAffineMetricRegion q.left.toAdd q.right Ω)
      (wickTransportedMetricDomain q.left.toAdd q.right Ω)
      (wickPoincareRayAction a q.left.toAdd q.right r)
      (wickChartMetricPathProtocolPoincare a q (wickOriginalMetricPathInChart π)) =
      wickIdentifiedMetricPathRecordReadout a s Ω
        (wickMetricPathF a s Ω (wickMetricPathPiA a s Ω
          (wickCommonRoleSourcePresentation a s Ω r))).val π :=
  (wick_complete_metric_path_ray_poincare a s q Ω (wickOriginalMetricNeighborhood Ω) r
    (wickOriginalMetricPathInChart π)).trans
    (wick_original_chart_readout_is_identified_source a s Ω r π)

end AASCKleinGordon
