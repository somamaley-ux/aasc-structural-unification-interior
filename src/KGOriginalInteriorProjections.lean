import KGConstraintStandingSource

/-! Independent projections of the existing original complete-record carrier.
The metric act map, first-response tensor and quantum ray are different arrows.
No paired-interior certificate or desired source identity is an input. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace AASCSemanticExhaustion

def kgInteriorFirstResponse (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    WickMetricPathQresp a s Ω → (MetricSourceProbe Ω →L[ℝ] ℝ) :=
  Quotient.lift (fun u => (wickOriginalRoleSource a s Ω u).attachment.functional) (by
    intro u v same
    exact (wick_full_role_implies_source_agreement
      (wickOriginalRoleSource a s Ω u) (wickOriginalRoleSource a s Ω v)
      ((wick_metric_path_record_iff_original a s Ω u v).mp same)).2.2.1)

def kgInteriorMetricSource (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    WickMetricPathQresp a s Ω → SymmetricSourceComponents Ω :=
  Quotient.lift (fun u => (wickOriginalRoleSource a s Ω u).attachment.represented) (by
    intro u v same
    exact (wick_full_role_implies_source_agreement
      (wickOriginalRoleSource a s Ω u) (wickOriginalRoleSource a s Ω v)
      ((wick_metric_path_record_iff_original a s Ω u v).mp same)).2.2.2.1)

def kgInteriorQuantum (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    WickMetricPathQresp a s Ω → PhysicalRay (fockCoreDomain a) :=
  Quotient.lift (fun u => rayMap _ (kgRawOriginalEquiv a u)) (by
    intro u v same
    exact (kg_raw_same_original_equivalence a s Ω u v).mpr same)

theorem kg_interior_quantum_original_square (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u : WickNonzeroCore) :
    kgInteriorQuantum a s Ω (Quotient.mk (wickMetricPathRoleSetoid a s Ω) u)=
      rayMap _ (kgRawOriginalEquiv a u) := rfl

theorem kg_interior_metric_original_square (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u : WickNonzeroCore) :
    kgInteriorMetricSource a s Ω (Quotient.mk (wickMetricPathRoleSetoid a s Ω) u)=
      wickRoleTA (wickOriginalRoleSource a s Ω u) := rfl

theorem kg_interior_metric_half_pairing (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (x : WickMetricPathQresp a s Ω) (H : MetricSourceProbe Ω) :
    (1/2 : ℝ)*metricSourcePairing (kgInteriorMetricSource a s Ω x) H=
      kgInteriorFirstResponse a s Ω x H := by
  induction x using Quotient.inductionOn with
  | _ u => exact (wickOriginalRoleSource a s Ω u).attachment.half_pairing H

theorem kg_interior_first_response_is_original (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (x : WickMetricPathQresp a s Ω) (H : MetricSourceProbe Ω) :
    wickIdentifiedMetricPathRecordReadout a s Ω x
      (.original (.metric (.first (wickKGIdentityAct H))))=
      .metric (.first (kgInteriorFirstResponse a s Ω x H)) := by
  induction x using Quotient.inductionOn with
  | _ u =>
    change wickMetricPathRoleOutput a s Ω u
      (.original (.metric (.first (wickKGIdentityAct H))))=_
    rw [wick_metric_path_entire_record_comparison]
    change WickRoleReadout.metric (.first (wickKGFirstOutput a s
      (originalWickUnitRepresentative a u.val) (wickKGIdentityAct H)))=_
    change WickRoleReadout.metric (.first (wickKGFirstOutput a s
      (originalWickUnitRepresentative a u.val) (wickKGIdentityAct H)))=
      WickRoleReadout.metric (.first ((wickOriginalRoleSource a s Ω u).attachment.functional H))
    apply congrArg (fun z : ℝ => WickRoleReadout.metric (.first z))
    rw [wick_KG_original_first_output_computed,wick_KG_identity_tangent]
    have source := (wickOriginalRoleSource a s Ω u).attachment.same_original_source
    change (wickOriginalRoleSource a s Ω u).attachment.functional=
      originalWickNativeRealMetricResponse a s (originalWickUnitRepresentative a u.val) Ω at source
    exact (congrArg (fun f : MetricSourceProbe Ω →L[ℝ] ℝ => f H) source).symm

theorem kg_interior_metric_source_faithful (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (x y : WickMetricPathQresp a s Ω) :
    kgInteriorMetricSource a s Ω x=kgInteriorMetricSource a s Ω y ↔
      ∀ H : MetricSourceProbe Ω,
        kgInteriorFirstResponse a s Ω x H=kgInteriorFirstResponse a s Ω y H := by
  constructor
  · intro same H
    exact (kg_interior_metric_half_pairing a s Ω x H).symm.trans
      ((congrArg (fun T => (1/2 : ℝ)*metricSourcePairing T H) same).trans
        (kg_interior_metric_half_pairing a s Ω y H))
  · intro same
    have functionals : kgInteriorFirstResponse a s Ω x=kgInteriorFirstResponse a s Ω y := by
      ext H
      exact same H
    exact (constructed_metric_source_unique _ _ (kg_interior_metric_half_pairing a s Ω x)).trans
      ((congrArg representedMetricSource functionals).trans
        (constructed_metric_source_unique _ _ (kg_interior_metric_half_pairing a s Ω y)).symm)

attribute [local irreducible] kgRawOriginalEquiv

theorem kg_interior_quantum_record_left_inverse (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : PhysicalRay (fockCoreDomain a)) :
    kgInteriorQuantum a s Ω (kgOriginalQuantumRecord a s Ω r)=r := by
  induction r using Quotient.inductionOn with
  | _ x =>
    change kgInteriorQuantum a s Ω (kgOriginalQuantumRecord a s Ω (rayMap _ x))=rayMap _ x
    have original := kg_original_quantum_record_on_representatives a s Ω ((kgRawOriginalEquiv a).symm x)
    rw [Equiv.apply_symm_apply] at original
    rw [original,kg_interior_quantum_original_square,Equiv.apply_symm_apply]

theorem kg_interior_quantum_record_right_inverse (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (x : WickMetricPathQresp a s Ω) :
    kgOriginalQuantumRecord a s Ω (kgInteriorQuantum a s Ω x)=x := by
  induction x using Quotient.inductionOn with
  | _ u => exact kg_original_quantum_record_on_representatives a s Ω u

def kgOriginalInteriorQuantumEquiv (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    WickMetricPathQresp a s Ω ≃ PhysicalRay (fockCoreDomain a) where
  toFun := kgInteriorQuantum a s Ω
  invFun := kgOriginalQuantumRecord a s Ω
  left_inv := kg_interior_quantum_record_right_inverse a s Ω
  right_inv := kg_interior_quantum_record_left_inverse a s Ω

theorem kg_interior_quantum_faithful (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) : Function.Injective (kgInteriorQuantum a s Ω) :=
  (kgOriginalInteriorQuantumEquiv a s Ω).injective

theorem kg_interior_derived_standing_left_inverse (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : PhysicalRay (fockCoreDomain a)) :
    kgInteriorQuantum a s Ω (kgW9OriginalResponse a s Ω r)=r := by
  rw [kg_w9_original_response_comparison]
  exact kg_interior_quantum_record_left_inverse a s Ω r

theorem kg_interior_derived_standing_right_inverse (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (x : WickMetricPathQresp a s Ω) :
    kgW9OriginalResponse a s Ω (kgInteriorQuantum a s Ω x)=x := by
  rw [kg_w9_original_response_comparison]
  exact kg_interior_quantum_record_right_inverse a s Ω x

theorem kg_interior_complete_source_square (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (x : WickMetricPathQresp a s Ω) :
    (wickMetricPathF a s Ω (wickMetricPathPiA a s Ω
      (wickCommonRoleSourcePresentation a s Ω
        (kgOriginalQuantumToRay a (kgInteriorQuantum a s Ω x))))).val=x := by
  exact (kg_w9_complete_original_source_square a s Ω (kgInteriorQuantum a s Ω x)).symm.trans
    (kg_interior_derived_standing_right_inverse a s Ω x)

end AASCKleinGordon
