import RegisteredOrbitStandingDescent

/-! The quotient reference system is computed from the derived standing
record. Its reference and failure fibres are proved to agree with the raw one. -/
noncomputable section
namespace AASCKleinGordon.W9.RawRegisteredOrbit
variable {X Q V P : Type} (D : RawRegisteredOrbit X Q V P)

def standingReferences : AASC.PartialReferenceSystem P (RegisteredQuestion Q) V := by
  classical
  exact ⟨fun r => fun
    | .execution π => if D.succeeds (D.standingRecord r π) then some (D.standingRecord r π) else none
    | .ledger π => some (D.standingRecord r π)⟩

def standingKernel : AASC.Kernel D.standingReferences.incidenceSystem :=
  D.standingReferences.kernel

theorem standing_reference_square (x : X) (π : RegisteredQuestion Q) :
    D.standingReferences.referenceAt (D.q x) π=D.references.referenceAt x π := by
  classical
  cases π with
  | execution π =>
    change (if D.succeeds (D.standingRecord (D.q x) π) then
      some (D.standingRecord (D.q x) π) else none)=_
    rw [D.standing_record_spec]
    rfl
  | ledger π => exact congrArg some (D.standing_record_spec x π)

theorem standing_incidence_square (x : X) (π : RegisteredQuestion Q) (v : V) :
    D.standingReferences.incidenceSystem.incidence (D.q x) π v ↔
      D.references.incidenceSystem.incidence x π v := by
  change D.standingReferences.referenceAt (D.q x) π=some v ↔ D.references.referenceAt x π=some v
  rw [D.standing_reference_square]

theorem standing_kernel_square (x : X) (π : RegisteredQuestion Q) (v : V) :
    D.standingKernel.standing (D.q x) π v ↔ D.kernel.standing x π v :=
  D.standing_incidence_square x π v

theorem standing_admissibility_square (x : X) (π : RegisteredQuestion Q) :
    D.standingReferences.incidenceSystem.AdmissibleAt (D.q x) π ↔
      D.references.incidenceSystem.AdmissibleAt x π := by
  exact exists_congr (D.standing_incidence_square x π)

theorem standing_failure_square (x : X) (π : RegisteredQuestion Q) :
    D.standingKernel.FailureAt (D.q x) π ↔ D.kernel.FailureAt x π := by
  change (∀ v,¬ D.standingReferences.incidenceSystem.incidence (D.q x) π v) ↔
    (∀ v,¬ D.references.incidenceSystem.incidence x π v)
  simp only [D.standing_incidence_square]

theorem standing_reference_determinate : D.standingReferences.incidenceSystem.Determinate :=
  D.standingReferences.determinate

theorem standing_reference_unique : D.standingKernel.ReferenceUnique :=
  D.standingKernel.reference_unique_of_determinate D.standing_reference_determinate

end AASCKleinGordon.W9.RawRegisteredOrbit
