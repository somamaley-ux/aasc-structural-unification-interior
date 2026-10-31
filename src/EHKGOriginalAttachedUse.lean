import EHKGFiniteContinuationUse
import EHKGConstraintFirstAttachment
import EHKGCommonActionAxes

/-! The actual original licensed metric record is retained in full. New
classical uses are received only at the same metric, with explicit rejection
otherwise. Original quantum preparation and classical Cauchy data remain
different objects. Old operation words precede the new scalar program; no
interleaved metric-changing scalar dynamics is asserted. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing
open scoped Topology
namespace AASCKleinGordon.CurvedKG
attribute [local instance] Classical.propDecidable

def scalarEventsAtOriginalMetric (a : Parameters) (metric : CoordinatePoint → Tensor2)
    (state : CurvedScalarUseState a) (program : List CurvedKGOperation) : List CurvedKGUseEvent :=
  if metric = originalEHActMetric (conformalOperand (conformalFrequency a)) then (curvedKGRun a state program).2
  else [⟨none, some (.inl .incompatibleMetric)⟩]

def licensedCurvedUseRecord (a : Parameters) (s kappa Lambda : ℝ) (coupling : kappa ≠ 0)
    (state : CurvedScalarUseState a) (ops : List (PreparedHistoryOperation a (⊤ : Opens CoordinatePoint)))
    (program : List CurvedKGOperation) : RawMetricUseReadout a s (⊤ : Opens CoordinatePoint) × List CurvedKGUseEvent :=
  let original := licensedReadout a s (⊤ : Opens CoordinatePoint) (curvedLicensedMetricReceiver a s kappa Lambda coupling) ops
  (original, scalarEventsAtOriginalMetric a original.metric state program)

def rawCurvedUseRecord (a : Parameters) (s kappa Lambda : ℝ)
    (state : CurvedScalarUseState a) (ops : List (PreparedHistoryOperation a (⊤ : Opens CoordinatePoint)))
    (program : List CurvedKGOperation) : RawMetricUseReadout a s (⊤ : Opens CoordinatePoint) × List CurvedKGUseEvent :=
  let original := rawMetricUseProfile a s (⊤ : Opens CoordinatePoint) kappa Lambda (curvedOriginalMetricHistory a) ops
  (original, scalarEventsAtOriginalMetric a original.metric state program)

theorem licensed_curved_original_record_square (a : Parameters) (s kappa Lambda : ℝ) (coupling : kappa ≠ 0)
    (state : CurvedScalarUseState a) (ops : List (PreparedHistoryOperation a (⊤ : Opens CoordinatePoint)))
    (program : List CurvedKGOperation) :
    licensedCurvedUseRecord a s kappa Lambda coupling state ops program =
      rawCurvedUseRecord a s kappa Lambda state ops program := rfl

theorem licensed_curved_retains_complete_original (a : Parameters) (s kappa Lambda : ℝ) (coupling : kappa ≠ 0)
    (state : CurvedScalarUseState a) (ops : List (PreparedHistoryOperation a (⊤ : Opens CoordinatePoint)))
    (program : List CurvedKGOperation) :
    (licensedCurvedUseRecord a s kappa Lambda coupling state ops program).1 =
      licensedReadout a s (⊤ : Opens CoordinatePoint) (curvedLicensedMetricReceiver a s kappa Lambda coupling) ops := rfl

theorem licensed_curved_empty_original_all_uses (a : Parameters) (s kappa Lambda : ℝ) (coupling : kappa ≠ 0)
    (state : CurvedScalarUseState a) (program : List CurvedKGOperation) :
    (licensedCurvedUseRecord a s kappa Lambda coupling state [] program).2 = (curvedKGRun a state program).2 := by
  change scalarEventsAtOriginalMetric a _ state program = _
  rw [curved_licensed_metric_exact]
  simp [scalarEventsAtOriginalMetric]

theorem original_incompatible_metric_stays_failed (a : Parameters) (metric : CoordinatePoint → Tensor2)
    (state : CurvedScalarUseState a) (program : List CurvedKGOperation)
    (incompatible : metric ≠ originalEHActMetric (conformalOperand (conformalFrequency a))) :
    scalarEventsAtOriginalMetric a metric state program = [⟨none, some (.inl .incompatibleMetric)⟩] := by
  simp only [scalarEventsAtOriginalMetric, if_neg incompatible]

theorem actual_original_metric_scalar_equation (a : Parameters) (s kappa Lambda : ℝ) (coupling : kappa ≠ 0)
    (state : CurvedScalarUseState a) (ops : List (PreparedHistoryOperation a (⊤ : Opens CoordinatePoint)))
    (compatible : (licensedReadout a s (⊤ : Opens CoordinatePoint) (curvedLicensedMetricReceiver a s kappa Lambda coupling) ops).metric =
      originalEHActMetric (conformalOperand (conformalFrequency a))) (p : CoordinatePoint) (inside : p ∈ state.domain) :
    scalarFieldWaveOperator
      (licensedReadout a s (⊤ : Opens CoordinatePoint) (curvedLicensedMetricReceiver a s kappa Lambda coupling) ops).metric state.field p =
        (massWaveNumber a) ^ 2 * state.field p := by
  rw [compatible]
  exact state.equation p inside

theorem attached_use_local_extension_independent (a : Parameters) (s kappa Lambda : ℝ) (coupling : kappa ≠ 0)
    (state other : CurvedScalarUseState a) (same : ScalarUseSame a state other)
    (ops : List (PreparedHistoryOperation a (⊤ : Opens CoordinatePoint))) (program : List CurvedKGOperation) :
    licensedCurvedUseRecord a s kappa Lambda coupling state ops program =
      licensedCurvedUseRecord a s kappa Lambda coupling other ops program := by
  change (_, scalarEventsAtOriginalMetric a _ state program) = (_, scalarEventsAtOriginalMetric a _ other program)
  congr 1
  unfold scalarEventsAtOriginalMetric
  split_ifs
  · exact (curved_kg_run_same a program state other same).2
  · rfl

end AASCKleinGordon.CurvedKG
