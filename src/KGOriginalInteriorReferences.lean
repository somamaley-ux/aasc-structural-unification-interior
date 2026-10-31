import KGOriginalInteriorFrame

/-! References are transported only after the independent original/quantum
comparison has been proved. Their raw square, and hence admissibility and
failure, is the accepted original registered reference system. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace AASCSemanticExhaustion

def kgInteriorSourceAttachment (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    WickMetricPathQresp a s Ω → WickRoleQsrc a s Ω :=
  Quotient.lift (fun u => wickRolePiA a s Ω (wickOriginalRoleSource a s Ω u)) (by
    intro u v same
    exact Quotient.sound (wick_full_role_implies_source_agreement
      (wickOriginalRoleSource a s Ω u) (wickOriginalRoleSource a s Ω v)
      ((wick_metric_path_record_iff_original a s Ω u v).mp same)))

def kgInteriorSourceLedger (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    WickMetricPathQresp a s Ω → WickSourceLedgerValue Ω :=
  Quotient.lift (fun u => (wickOriginalRoleSource a s Ω u).ledger) (by
    intro u v same
    exact (wick_full_role_implies_source_agreement
      (wickOriginalRoleSource a s Ω u) (wickOriginalRoleSource a s Ω v)
      ((wick_metric_path_record_iff_original a s Ω u v).mp same)).2.2.2.2)

theorem kg_interior_source_ledger_raw (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (u : WickNonzeroCore) :
    kgInteriorSourceLedger a s Ω (Quotient.mk (wickMetricPathRoleSetoid a s Ω) u)=
      (wickOriginalRoleSource a s Ω u).ledger := rfl

theorem kg_interior_source_ledger_exact (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (x : WickMetricPathQresp a s Ω) :
    kgInteriorSourceLedger a s Ω x=wickOriginalSourceLedgerValue Ω := by
  induction x using Quotient.inductionOn with
  | _ u => exact (wickOriginalRoleSource a s Ω u).ledger_exact

theorem kg_interior_source_attachment_tensor (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (x : WickMetricPathQresp a s Ω) :
    wickRoleQg a s Ω (kgInteriorSourceAttachment a s Ω x)=kgInteriorMetricSource a s Ω x := by
  induction x using Quotient.inductionOn with | _ u => rfl

def kgInteriorReferences (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    AASC.PartialReferenceSystem (WickMetricPathQresp a s Ω)
      (RegisteredQuestion (KGFamilyQuestion a Ω (kgOriginalObject a))) KGFamilyReadout :=
  ⟨fun x π => (kgRawRegisteredOrbit a s Ω (kgOriginalObject a)).standingReferences.referenceAt
    (kgInteriorQuantum a s Ω x) π⟩

def kgInteriorKernel (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    AASC.Kernel (kgInteriorReferences a s Ω).incidenceSystem :=
  (kgInteriorReferences a s Ω).kernel

theorem kg_interior_reference_raw_square (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u : WickNonzeroCore)
    (π : RegisteredQuestion (KGFamilyQuestion a Ω (kgOriginalObject a))) :
    (kgInteriorReferences a s Ω).referenceAt (Quotient.mk (wickMetricPathRoleSetoid a s Ω) u) π=
      (kgRawRegisteredOrbit a s Ω (kgOriginalObject a)).references.referenceAt
        (kgRawOriginalEquiv a u) π :=
  (kgRawRegisteredOrbit a s Ω (kgOriginalObject a)).standing_reference_square
    (kgRawOriginalEquiv a u) π

theorem kg_interior_kernel_raw_square (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u : WickNonzeroCore)
    (π : RegisteredQuestion (KGFamilyQuestion a Ω (kgOriginalObject a))) (v : KGFamilyReadout) :
    (kgInteriorKernel a s Ω).standing (Quotient.mk (wickMetricPathRoleSetoid a s Ω) u) π v ↔
      (kgRawRegisteredOrbit a s Ω (kgOriginalObject a)).kernel.standing
        (kgRawOriginalEquiv a u) π v := by
  change (kgInteriorReferences a s Ω).referenceAt _ π=some v ↔
    (kgRawRegisteredOrbit a s Ω (kgOriginalObject a)).references.referenceAt _ π=some v
  rw [kg_interior_reference_raw_square]

theorem kg_interior_admissibility_raw_square (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u : WickNonzeroCore)
    (π : RegisteredQuestion (KGFamilyQuestion a Ω (kgOriginalObject a))) :
    (kgInteriorReferences a s Ω).incidenceSystem.AdmissibleAt
        (Quotient.mk (wickMetricPathRoleSetoid a s Ω) u) π ↔
      (kgRawRegisteredOrbit a s Ω (kgOriginalObject a)).references.incidenceSystem.AdmissibleAt
        (kgRawOriginalEquiv a u) π :=
  exists_congr (kg_interior_kernel_raw_square a s Ω u π)

theorem kg_interior_failure_raw_square (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u : WickNonzeroCore)
    (π : RegisteredQuestion (KGFamilyQuestion a Ω (kgOriginalObject a))) :
    (kgInteriorKernel a s Ω).FailureAt (Quotient.mk (wickMetricPathRoleSetoid a s Ω) u) π ↔
      (kgRawRegisteredOrbit a s Ω (kgOriginalObject a)).kernel.FailureAt
        (kgRawOriginalEquiv a u) π := by
  change (∀ v,¬ (kgInteriorKernel a s Ω).standing _ π v) ↔
    (∀ v,¬ (kgRawRegisteredOrbit a s Ω (kgOriginalObject a)).kernel.standing _ π v)
  simp only [kg_interior_kernel_raw_square]

theorem kg_interior_reference_determinate (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    (kgInteriorReferences a s Ω).incidenceSystem.Determinate :=
  (kgInteriorReferences a s Ω).determinate

theorem kg_interior_reference_unique (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    (kgInteriorKernel a s Ω).ReferenceUnique :=
  (kgInteriorKernel a s Ω).reference_unique_of_determinate (kg_interior_reference_determinate a s Ω)

def kgInteriorRegisteredReadout (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (x : WickMetricPathQresp a s Ω) : KGFamilyQuestion a Ω (kgOriginalObject a) → KGFamilyReadout :=
  kgW9StandingRecord a s Ω (kgOriginalObject a) (kgInteriorQuantum a s Ω x)

theorem kg_interior_registered_raw_square (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u : WickNonzeroCore)
    (π : KGFamilyQuestion a Ω (kgOriginalObject a)) :
    kgInteriorRegisteredReadout a s Ω (Quotient.mk (wickMetricPathRoleSetoid a s Ω) u) π=
      kgFamilyOutput a s Ω (kgOriginalObject a) (kgRawOriginalEquiv a u) π :=
  kg_w9_standing_complete_record a s Ω (kgOriginalObject a) (kgRawOriginalEquiv a u) π

theorem kg_interior_registered_original_square (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (x : WickMetricPathQresp a s Ω) (π : WickMetricPathRoleProtocol Ω) :
    kgInteriorRegisteredReadout a s Ω x (.original .original π)=
      .extraction (some (wickIdentifiedMetricPathRecordReadout a s Ω x π)) := by
  induction x using Quotient.inductionOn with
  | _ u =>
    rw [kg_interior_registered_raw_square]
    exact kg_family_original_identity a s Ω u π

theorem kg_interior_first_failure_raw_square (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u : WickNonzeroCore)
    (word : List (KGFamilyQuestion a Ω (kgOriginalObject a))) :
    kgFirstFailure (kgInteriorRegisteredReadout a s Ω
      (Quotient.mk (wickMetricPathRoleSetoid a s Ω) u)) word=
      kgFirstFailure (kgFamilyOutput a s Ω (kgOriginalObject a) (kgRawOriginalEquiv a u)) word := by
  have output := funext (kg_interior_registered_raw_square a s Ω u)
  rw [output]

end AASCKleinGordon
