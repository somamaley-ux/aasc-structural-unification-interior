import WickMetricPathCompleteRecords

/-! Source descent for the complete admitted-path record. The raw source,
functional, tensor and ledger are the previously constructed native objects.
The new content is identification of their complete path-augmented base and
metric graph, with no assumed original-source comparison certificate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickMetricPathMetInc {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω)
    (π : WickMetricPathRoleProtocol Ω) : Prop :=
  ∃ δ,wickMetricPathQuestionCompare π = .metric (.first δ) ∧ wickKGFirstTangent δ = H

def wickMetricPathMetResp (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (u : WickNonzeroCore) (H : MetricSourceProbe Ω) (z : ℝ) : Prop :=
  ∃ π,wickMetricPathMetInc H π ∧ wickMetricPathRoleOutput a s Ω u π = .metric (.first z)

theorem wick_metric_path_metric_graph (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u : WickNonzeroCore) (H : MetricSourceProbe Ω) (z : ℝ) :
    wickMetricPathMetResp a s Ω u H z ↔
      originalWickNativeRealMetricResponse a s (originalWickUnitRepresentative a u.val) Ω H = z := by
  constructor
  · rintro ⟨π,⟨δ,inc,tangent⟩,output⟩
    rw [wick_metric_path_entire_record_comparison,inc] at output
    have hz : wickKGFirstOutput a s (originalWickUnitRepresentative a u.val) δ = z :=
      WickKGOriginalReadout.first.inj (WickRoleReadout.metric.inj output)
    exact (congrArg (originalWickNativeRealMetricResponse a s
      (originalWickUnitRepresentative a u.val) Ω) tangent).symm.trans
        ((wick_KG_original_first_output_computed a s
          (originalWickUnitRepresentative a u.val) δ).symm.trans hz)
  · intro hz
    refine ⟨.original (.metric (.first (wickKGIdentityAct H))),
      ⟨wickKGIdentityAct H,rfl,wick_KG_identity_tangent H⟩,?_⟩
    rw [wick_metric_path_entire_record_comparison]
    exact congrArg (fun w => WickRoleReadout.metric (.first w))
      ((wick_KG_original_first_output_computed a s
        (originalWickUnitRepresentative a u.val) (wickKGIdentityAct H)).trans
          ((congrArg (originalWickNativeRealMetricResponse a s
            (originalWickUnitRepresentative a u.val) Ω) (wick_KG_identity_tangent H)).trans hz))

theorem wick_metric_path_raw_source_graph {a : Parameters} {s : ℝ}
    {Ω : Opens CoordinatePoint} (p : WickRoleSourcePresentation a s Ω)
    (H : MetricSourceProbe Ω) (z : ℝ) :
    wickMetricPathMetResp a s Ω p.response H z ↔ p.attachment.functional H = z := by
  rw [wick_metric_path_metric_graph,p.attachment.same_original_source]

def WickMetricPathSourceEquivalent {a : Parameters} {s : ℝ} {Ω : Opens CoordinatePoint}
    (p q : WickRoleSourcePresentation a s Ω) : Prop :=
  (wickMetricPathRoleSetoid a s Ω).r p.response q.response ∧
  (∀ H z,wickMetricPathMetResp a s Ω p.response H z ↔
    wickMetricPathMetResp a s Ω q.response H z) ∧
  p.attachment.functional = q.attachment.functional ∧
  p.attachment.represented = q.attachment.represented ∧ p.ledger = q.ledger

theorem wick_metric_path_source_equivalent_iff_original {a : Parameters} {s : ℝ}
    {Ω : Opens CoordinatePoint} (p q : WickRoleSourcePresentation a s Ω) :
    WickMetricPathSourceEquivalent p q ↔ WickRoleSourceEquivalent p q := by
  constructor
  · intro same
    exact wick_full_role_implies_source_agreement p q
      ((wick_metric_path_record_iff_original a s Ω p.response q.response).mp same.1)
  · intro same
    refine ⟨(wick_metric_path_record_iff_original a s Ω p.response q.response).mpr same.1,
      ?_,same.2.2.1,same.2.2.2.1,same.2.2.2.2⟩
    intro H z
    rw [wick_metric_path_raw_source_graph,wick_metric_path_raw_source_graph,same.2.2.1]

def wickMetricPathSourceSetoid (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    Setoid (WickRoleSourcePresentation a s Ω) where
  r := WickMetricPathSourceEquivalent
  iseqv := ⟨fun p => (wick_metric_path_source_equivalent_iff_original p p).mpr
      ((wickRoleSourceSetoid a s Ω).iseqv.refl p),
    fun {p q} h => (wick_metric_path_source_equivalent_iff_original q p).mpr
      ((wickRoleSourceSetoid a s Ω).iseqv.symm
        ((wick_metric_path_source_equivalent_iff_original p q).mp h)),
    fun {p q r} h k => (wick_metric_path_source_equivalent_iff_original p r).mpr
      ((wickRoleSourceSetoid a s Ω).iseqv.trans
        ((wick_metric_path_source_equivalent_iff_original p q).mp h)
        ((wick_metric_path_source_equivalent_iff_original q r).mp k))⟩

abbrev WickMetricPathQsrc (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :=
  Quotient (wickMetricPathSourceSetoid a s Ω)

def wickMetricPathSourceEquiv (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    WickMetricPathQsrc a s Ω ≃ WickRoleQsrc a s Ω where
  toFun := Quotient.map id (fun p q => (wick_metric_path_source_equivalent_iff_original p q).mp)
  invFun := Quotient.map id (fun p q => (wick_metric_path_source_equivalent_iff_original p q).mpr)
  left_inv q := by induction q using Quotient.inductionOn with | _ p => rfl
  right_inv q := by induction q using Quotient.inductionOn with | _ p => rfl

def wickMetricPathPiA (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (p : WickRoleSourcePresentation a s Ω) : WickMetricPathQsrc a s Ω := Quotient.mk _ p

def wickMetricPathForget (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    WickMetricPathQsrc a s Ω → WickMetricPathQresp a s Ω :=
  Quotient.map WickRoleSourcePresentation.response (fun _ _ h => h.1)

def wickMetricPathQsrcbase (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    Set (WickMetricPathQresp a s Ω) := Set.range (wickMetricPathForget a s Ω)

def wickMetricPathF (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (q : WickMetricPathQsrc a s Ω) : wickMetricPathQsrcbase a s Ω :=
  ⟨wickMetricPathForget a s Ω q,⟨q,rfl⟩⟩

theorem wick_metric_path_forget_comparison (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (q : WickMetricPathQsrc a s Ω) :
    wickMetricPathResponseEquiv a s Ω (wickMetricPathForget a s Ω q) =
      wickRoleForget a s Ω (wickMetricPathSourceEquiv a s Ω q) := by
  induction q using Quotient.inductionOn with | _ p => rfl

/-- F(pi_A(s_tilde(r))) is the independently computed complete KG path record.
The source is the existing prequotient native family; no richer original
ledger, active curved metric or quantum-interior identification is asserted. -/
theorem wick_metric_path_original_source_identification (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCoreRaySetoid) :
    (wickMetricPathF a s Ω (wickMetricPathPiA a s Ω
      (wickCommonRoleSourcePresentation a s Ω r))).val = wickMetricPathRoleEval a s Ω r :=
  congrArg (wickMetricPathRoleEval a s Ω) (Quotient.out_eq r)

theorem wick_metric_path_source_complete_output (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCoreRaySetoid)
    (π : WickMetricPathRoleProtocol Ω) :
    wickMetricPathRoleOutput a s Ω (wickCommonRoleSourcePresentation a s Ω r).response π =
      wickCommonRoleReadout a s Ω r (wickMetricPathQuestionCompare π) := by
  rw [wick_metric_path_entire_record_comparison]
  exact wick_common_role_source_entire_output a s Ω r (wickMetricPathQuestionCompare π)

end AASCKleinGordon
