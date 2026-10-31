import SKGSourceUseReaders
import SKGGravitationalReceiver

/-! The complete earlier licensed-use record is the first component.
Source questions read the supplied regular local history, independently of
the retained scalar-program transcript. No arbitrary metric-change transport
or equality with the old quantum-preparation source is asserted. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG AASCKleinGordon.CanonicalLicensing
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

def licensedSameActionSourceRecord (a : Parameters) (s kappa Lambda : ℝ) (coupling : kappa ≠ 0)
    (state : RegularScalarSourceState a)
    (ops : List (PreparedHistoryOperation a (⊤ : Opens CoordinatePoint)))
    (program : List CurvedKGOperation) (questions : List (ScalarSourceQuestion a)) :=
  let old := licensedCurvedUseRecord a s kappa Lambda coupling state.localState ops program
  (old, scalarSourceReadList a old.1.metric state questions)

def rawSameActionSourceRecord (a : Parameters) (s kappa Lambda : ℝ)
    (state : RegularScalarSourceState a)
    (ops : List (PreparedHistoryOperation a (⊤ : Opens CoordinatePoint)))
    (program : List CurvedKGOperation) (questions : List (ScalarSourceQuestion a)) :=
  let old := rawCurvedUseRecord a s kappa Lambda state.localState ops program
  (old, scalarSourceReadList a old.1.metric state questions)

theorem licensed_source_complete_record_square (a : Parameters) (s kappa Lambda : ℝ) (coupling : kappa ≠ 0)
    (state : RegularScalarSourceState a) (ops : List (PreparedHistoryOperation a (⊤ : Opens CoordinatePoint)))
    (program : List CurvedKGOperation) (questions : List (ScalarSourceQuestion a)) :
    licensedSameActionSourceRecord a s kappa Lambda coupling state ops program questions =
      rawSameActionSourceRecord a s kappa Lambda state ops program questions := rfl

theorem licensed_source_retains_complete_predecessor (a : Parameters) (s kappa Lambda : ℝ) (coupling : kappa ≠ 0)
    (state : RegularScalarSourceState a) (ops : List (PreparedHistoryOperation a (⊤ : Opens CoordinatePoint)))
    (program : List CurvedKGOperation) (questions : List (ScalarSourceQuestion a)) :
    (licensedSameActionSourceRecord a s kappa Lambda coupling state ops program questions).1 =
      licensedCurvedUseRecord a s kappa Lambda coupling state.localState ops program := rfl

theorem licensed_source_empty_word_actual_readers (a : Parameters) (s kappa Lambda : ℝ) (coupling : kappa ≠ 0)
    (state : RegularScalarSourceState a) (program : List CurvedKGOperation) (questions : List (ScalarSourceQuestion a)) :
    (licensedSameActionSourceRecord a s kappa Lambda coupling state [] program questions).2 =
      scalarSourceReadList a (sourceMetric a) state questions := by
  change scalarSourceReadList a (licensedReadout a s (⊤ : Opens CoordinatePoint)
    (curvedLicensedMetricReceiver a s kappa Lambda coupling) []).metric state questions = _
  rw [curved_licensed_metric_exact]

theorem licensed_source_local_extension_independent (a : Parameters) (s kappa Lambda : ℝ) (coupling : kappa ≠ 0)
    (state other : RegularScalarSourceState a) (same : ScalarUseSame a state.localState other.localState)
    (ops : List (PreparedHistoryOperation a (⊤ : Opens CoordinatePoint)))
    (program : List CurvedKGOperation) (questions : List (ScalarSourceQuestion a)) :
    licensedSameActionSourceRecord a s kappa Lambda coupling state ops program questions =
      licensedSameActionSourceRecord a s kappa Lambda coupling other ops program questions := by
  apply Prod.ext
  · exact attached_use_local_extension_independent a s kappa Lambda coupling _ _ same ops program
  · exact (scalar_source_records_and_failures_local a _ state other same questions).1

theorem licensed_source_continuation_square (a : Parameters) (s kappa Lambda : ℝ) (coupling : kappa ≠ 0)
    (state : RegularScalarSourceState a) (request : ScalarContinuationRequest) (nonzero : request.scale ≠ 0)
    (inside : scalarContinuationDomain a request ≤ state.localState.domain)
    (matching : scalarContinuationDataMatch a state.localState request)
    (ops : List (PreparedHistoryOperation a (⊤ : Opens CoordinatePoint)))
    (program : List CurvedKGOperation) (questions : List (ScalarSourceQuestion a)) :
    licensedSameActionSourceRecord a s kappa Lambda coupling
      (continuedScalarSourceState a state request inside) ops program questions =
    licensedSameActionSourceRecord a s kappa Lambda coupling
      (restrictScalarSourceState a state (scalarContinuationDomain a request) inside) ops program questions :=
  licensed_source_local_extension_independent a s kappa Lambda coupling _ _
    (continued_state_is_restriction a state.localState request nonzero inside matching) ops program questions

end AASCKleinGordon.SameActionSource
