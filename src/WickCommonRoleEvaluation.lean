import WickCovariantRoleTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

/-- An unevaluated action/representation program. Neither a source functional
nor a selected physical state occurs in its data. This native constructor is
not an identification with the unrestricted corpus response quotient. -/
structure WickUpstreamActionRole (a : Parameters) (Ω : Opens CoordinatePoint) where
  finiteAction : FiniteParticleCore → MetricSourceProbe Ω → ℝ
  representation : ProperPoincareTransform →* (FockHilbert a ≃ₗᵢ[ℂ] FockHilbert a)

def wickNativeActionRole (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    WickUpstreamActionRole a Ω where
  finiteAction := fun u H => wickOriginalRealFiniteAction a s u H
  representation := originalFockPoincareRepresentation a

/-- State evaluation computes the action derivative and transition probability
directly. Finite failure is retained; no prospective source is queried. -/
def wickUpstreamActionEvaluate {a : Parameters} {Ω : Opens CoordinatePoint}
    (R : WickUpstreamActionRole a Ω) (u : WickNonzeroCore) :
    WickRoleProtocol Ω → WickRoleReadout := by
  classical
  exact fun
    | .metric (.finite H) =>
        if H ∈ wickOriginalMetricNeighborhood Ω then
          .metric (.finite (R.finiteAction (originalWickUnitRepresentative a u.val) H))
        else .metric .failed
    | .metric (.first δ) => .metric (.first
        (deriv (fun t => R.finiteAction (originalWickUnitRepresentative a u.val)
          (δ.parameter t • δ.test)) 0))
    | .comparison g v => .probability
        (‖inner ℂ (finiteParticleCoreToFock a (originalWickUnitRepresentative a v.val))
          (R.representation g
            (finiteParticleCoreToFock a (originalWickUnitRepresentative a u.val)))‖^2)

theorem wick_upstream_evaluation_entire_original (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u : WickNonzeroCore) (π : WickRoleProtocol Ω) :
    wickUpstreamActionEvaluate (wickNativeActionRole a s Ω) u π =
      wickOriginalRoleOutput a s Ω u π := by
  cases π with
  | metric π =>
    cases π with
    | finite H =>
      by_cases h : H ∈ wickOriginalMetricNeighborhood Ω
      · simp only [wickUpstreamActionEvaluate,wickNativeActionRole,wickOriginalRoleOutput,
          wickKGOriginalOutput,wickKGFiniteActionCarrier,if_pos h,dif_pos h]
      · simp only [wickUpstreamActionEvaluate,wickNativeActionRole,wickOriginalRoleOutput,
          wickKGOriginalOutput,if_neg h,dif_neg h]
    | first δ => rfl
  | comparison g v => rfl

theorem wick_upstream_first_act_computed (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u : WickNonzeroCore) (δ : WickKGFirstMetricAct Ω) :
    wickUpstreamActionEvaluate (wickNativeActionRole a s Ω) u (.metric (.first δ)) =
      .metric (.first (originalWickNativeRealMetricResponse a s
        (originalWickUnitRepresentative a u.val) Ω (wickKGFirstTangent δ))) := by
  rw [wick_upstream_evaluation_entire_original]
  exact congrArg (fun z => WickRoleReadout.metric (WickKGOriginalReadout.first z))
    (wick_KG_original_first_output_computed a s (originalWickUnitRepresentative a u.val) δ)

def wickCommonRoleReadout (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    Quotient wickCoreRaySetoid → WickRoleProtocol Ω → WickRoleReadout :=
  Quotient.lift (wickUpstreamActionEvaluate (wickNativeActionRole a s Ω)) (by
    intro u v same
    funext π
    rw [wick_upstream_evaluation_entire_original,wick_upstream_evaluation_entire_original]
    exact wick_role_same_ray_entire_signature a s Ω u v same π)

def wickCommonRoleEvaluation (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    Quotient wickCoreRaySetoid → WickRoleQresp a s Ω :=
  Quotient.lift (wickRoleClassify a s Ω) (by
    intro u v same
    exact Quotient.sound (wick_role_same_ray_entire_signature a s Ω u v same))

theorem wick_common_role_evaluation_is_original (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCoreRaySetoid) :
    wickCommonRoleEvaluation a s Ω r = wickOriginalRoleEval a s Ω r := by
  induction r using Quotient.inductionOn with | _ u => rfl

theorem wick_common_role_evaluation_injective (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) : Function.Injective (wickCommonRoleEvaluation a s Ω) := by
  intro r t h
  rw [wick_common_role_evaluation_is_original,wick_common_role_evaluation_is_original] at h
  exact wick_original_role_eval_injective a s Ω h

theorem wick_common_role_evaluation_surjective (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) : Function.Surjective (wickCommonRoleEvaluation a s Ω) := by
  intro z
  obtain ⟨r,hr⟩ := wick_original_role_eval_surjective a s Ω z
  exact ⟨r,(wick_common_role_evaluation_is_original a s Ω r).trans hr⟩

/-- Formation is the same fixed original prequotient protocol, for every
original common-core ray, including vacuum and mixed-sector superpositions. -/
def wickCommonRoleSourcePresentation (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCoreRaySetoid) :
    WickRoleSourcePresentation a s Ω := wickOriginalRoleSource a s Ω r.out

theorem wick_common_role_same_prequotient_family (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCoreRaySetoid) :
    wickCommonRoleSourcePresentation a s Ω r = wickRoleSx a s Ω r := rfl

theorem wick_common_role_source_response (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCoreRaySetoid) :
    (wickCommonRoleSourcePresentation a s Ω r).response = r.out := rfl

theorem wick_common_role_source_base_square (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCoreRaySetoid) :
    (wickRoleF a s Ω (wickRolePiA a s Ω (wickCommonRoleSourcePresentation a s Ω r))).val =
      wickCommonRoleEvaluation a s Ω r := by
  rw [wick_common_role_same_prequotient_family,wick_common_role_evaluation_is_original]
  exact wick_role_source_base_square a s Ω r

theorem wick_common_role_source_entire_output (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCoreRaySetoid) (π : WickRoleProtocol Ω) :
    wickOriginalRoleOutput a s Ω (wickCommonRoleSourcePresentation a s Ω r).response π =
      wickCommonRoleReadout a s Ω r π := by
  have h : wickCommonRoleReadout a s Ω (Quotient.mk wickCoreRaySetoid r.out) π =
      wickOriginalRoleOutput a s Ω r.out π :=
    wick_upstream_evaluation_entire_original a s Ω r.out π
  rw [Quotient.out_eq] at h
  exact h.symm

theorem wick_common_role_source_metric_readout (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCoreRaySetoid) (π : WickKGOriginalProtocol Ω) :
    WickRoleReadout.metric ((wickCommonRoleSourcePresentation a s Ω r).attachment.entire_readout π) =
      wickCommonRoleReadout a s Ω r (.metric π) := by
  rw [← wick_common_role_source_entire_output]
  exact congrArg WickRoleReadout.metric
    (congrFun (wick_original_presentation_readout_provenance a s
      (originalWickUnitRepresentative a r.out.val) Ω) π)

theorem wick_common_role_source_metric_graph (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCoreRaySetoid) (H : MetricSourceProbe Ω) (z : ℝ) :
    wickRoleSourceMetResp (wickCommonRoleSourcePresentation a s Ω r) H z ↔
      wickCommonRoleReadout a s Ω r (.metric (.first (wickKGIdentityAct H))) =
        .metric (.first z) := by
  rw [show wickRoleSourceMetResp (wickCommonRoleSourcePresentation a s Ω r) H z ↔
      (wickCommonRoleSourcePresentation a s Ω r).attachment.functional H = z from
        (wickCommonRoleSourcePresentation a s Ω r).attachment.source_graph H z]
  rw [← wick_common_role_source_metric_readout]
  change _ ↔ WickRoleReadout.metric
    (wickKGOriginalOutput a s (originalWickUnitRepresentative a r.out.val)
      (.first (wickKGIdentityAct H))) = _
  simp only [wickKGOriginalOutput,wick_KG_original_first_output_computed,wick_KG_identity_tangent,
    WickRoleReadout.metric.injEq,WickKGOriginalReadout.first.injEq]
  rw [(wickCommonRoleSourcePresentation a s Ω r).attachment.same_original_source,
    wick_common_role_source_response]

theorem wick_common_role_source_density_square (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCoreRaySetoid) :
    wickRoleQg a s Ω (wickRolePiA a s Ω (wickCommonRoleSourcePresentation a s Ω r)) =
      wickRoleTA (wickCommonRoleSourcePresentation a s Ω r) := rfl

theorem wick_common_role_source_half_pairing_derivative (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCoreRaySetoid) (H : MetricSourceProbe Ω) :
    (1/2 : ℝ)*metricSourcePairing (wickRoleTA (wickCommonRoleSourcePresentation a s Ω r)) H =
      deriv (fun t : ℝ => (wickNativeActionRole a s Ω).finiteAction
        (wickRayPresentationState a r) (t • H)) 0 := by
  rw [wickRoleTA,(wickCommonRoleSourcePresentation a s Ω r).attachment.half_pairing,
    (wickCommonRoleSourcePresentation a s Ω r).attachment.same_original_source,
    wick_common_role_source_response]
  change originalWickNativeRealMetricResponse a s (originalWickUnitRepresentative a r.out.val) Ω H =
    deriv (fun t : ℝ => wickOriginalRealFiniteAction a s
      (originalWickUnitRepresentative a r.out.val) (t • H)) 0
  exact (wick_original_real_finite_action_gateaux_derivative a s
    (originalWickUnitRepresentative a r.out.val) Ω H).deriv.symm

theorem wick_common_role_mass_overlap (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCoreRaySetoid) :
    wickRolePiA a s Ω (wickCommonRoleSourcePresentation a s Ω r) ∈ wickRoleQmasshat a s Ω :=
  wick_role_original_source_in_mass_overlap a s Ω r

theorem wick_common_role_metric_output_is_original_ray (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCoreRaySetoid) (π : WickKGOriginalProtocol Ω) :
    wickCommonRoleReadout a s Ω r (.metric π) =
      .metric (wickKGOriginalRayOutput a s Ω r π) := by
  induction r using Quotient.inductionOn with | _ u =>
    exact wick_upstream_evaluation_entire_original a s Ω u (.metric π)

/-- Chart transport is carried with the requests. This is a lawful unitary
operation; no total annihilation action on normalized rays is asserted. -/
def wickCommonRoleTransportedReadout (a : Parameters) (s : ℝ)
    (q : ProperPoincareTransform) (Ω : Opens CoordinatePoint)
    (r : Quotient wickCoreRaySetoid) :
    WickRoleProtocol (wickAffineMetricRegion q.left.toAdd q.right Ω) → WickRoleReadout
  | .metric π => .metric (wickKGTransportedRayOutput a s q.left.toAdd q.right Ω r π)
  | .comparison g v => wickCommonRoleReadout a s
      (wickAffineMetricRegion q.left.toAdd q.right Ω) r (.comparison g v)

theorem wick_common_role_entire_unitary_operation (a : Parameters) (s : ℝ)
    (q : ProperPoincareTransform) (Ω : Opens CoordinatePoint)
    (r : Quotient wickCoreRaySetoid) (π : WickRoleProtocol Ω) :
    wickCommonRoleTransportedReadout a s q Ω
      (wickPoincareRayAction a q.left.toAdd q.right r)
      (wickCovariantRoleProtocolTransport a q π) = wickCommonRoleReadout a s Ω r π := by
  cases π with
  | metric π =>
    change WickRoleReadout.metric (wickKGTransportedRayOutput a s q.left.toAdd q.right Ω
      (wickPoincareRayAction a q.left.toAdd q.right r) (wickKGProtocolPoincare q.left.toAdd q.right π)) = _
    rw [wick_KG_entire_ray_family_poincare,wick_common_role_metric_output_is_original_ray]
  | comparison g v =>
    induction r using Quotient.inductionOn with | _ u =>
      exact congrArg WickRoleReadout.probability (wick_original_role_comparison_poincare a q g u v)

theorem wick_common_role_source_unitary_functional (a : Parameters) (s : ℝ)
    (q : ProperPoincareTransform) (Ω : Opens CoordinatePoint)
    (r : Quotient wickCoreRaySetoid) (H : MetricSourceProbe Ω) :
    (wickCommonRoleSourcePresentation a s (wickAffineMetricRegion q.left.toAdd q.right Ω)
      (wickPoincareRayAction a q.left.toAdd q.right r)).attachment.functional
        (wickNativeAffineMetricTest q.left.toAdd q.right H) =
      (wickCommonRoleSourcePresentation a s Ω r).attachment.functional H := by
  rw [wick_common_role_same_prequotient_family,wick_common_role_same_prequotient_family,
    wick_role_source_same_original_ray_response,wick_role_source_same_original_ray_response]
  exact wick_original_ray_source_poincare a q.left.toAdd q.right s Ω r H

end AASCKleinGordon
