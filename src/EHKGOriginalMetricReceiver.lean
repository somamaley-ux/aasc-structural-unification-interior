import EHKGAllCompactCauchy
import KernelFaithfulLicensedEndpoints

/-! Exact attachment of the constructed operand to an actual existing
original metric-use history and its canonical licensed receiver. The old
scalar preparation is retained as such; it is not identified with the new
classical Cauchy field. A metric-changing old operation does not inherit the
fixed-background field equation without a new evolution proof. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing
open scoped Topology
namespace AASCKleinGordon.CurvedKG

def curvedOriginalMetricHistory (a : Parameters) : RestrictedRawHistory a (⊤ : Opens CoordinatePoint) :=
  ⟨1, ⟨kgFamilyVacuum a, ⟨conformalOperand (conformalFrequency a),
    (protected_same_eh_nonflat a).2.1⟩⟩, []⟩

def curvedLicensedMetricReceiver (a : Parameters) (s kappa Lambda : ℝ) (coupling : kappa ≠ 0) :
    LicensedMetricReceiver a s (⊤ : Opens CoordinatePoint) kappa Lambda :=
  presentLicensedHistory a s _ kappa Lambda coupling (curvedOriginalMetricHistory a)

theorem curved_original_metric_operand_exact (a : Parameters) (s kappa Lambda : ℝ) :
    (rawMetricUseReadout a s (⊤ : Opens CoordinatePoint) kappa Lambda
      (curvedOriginalMetricHistory a)).operand.val = conformalOperand (conformalFrequency a) := rfl

theorem curved_licensed_metric_exact (a : Parameters) (s kappa Lambda : ℝ) (coupling : kappa ≠ 0) :
    (licensedReadout a s (⊤ : Opens CoordinatePoint)
      (curvedLicensedMetricReceiver a s kappa Lambda coupling) []).metric =
        originalEHActMetric (conformalOperand (conformalFrequency a)) := rfl

theorem curved_licensed_original_record_square (a : Parameters) (s kappa Lambda : ℝ)
    (coupling : kappa ≠ 0) (ops : List (PreparedHistoryOperation a (⊤ : Opens CoordinatePoint))) :
    licensedReadout a s (⊤ : Opens CoordinatePoint)
      (curvedLicensedMetricReceiver a s kappa Lambda coupling) ops =
        rawMetricUseProfile a s (⊤ : Opens CoordinatePoint) kappa Lambda
          (curvedOriginalMetricHistory a) ops := rfl

theorem curved_receiver_has_canonical_license (a : Parameters) (s kappa Lambda : ℝ)
    (coupling : kappa ≠ 0) :
    AASCMetricityOriginalAssembly.constructedLicensing
      (originalMetricTask a s (⊤ : Opens CoordinatePoint) kappa Lambda)
      (curvedOriginalMetricHistory a)
      (originalMetricUseMeaning a s (⊤ : Opens CoordinatePoint) kappa Lambda) :=
  receiver_has_actual_canonical_license a s _ kappa Lambda coupling
    (curvedLicensedMetricReceiver a s kappa Lambda coupling)

theorem compact_curved_equation_on_actual_licensed_metric (a : Parameters) (s kappa Lambda : ℝ)
    (coupling : kappa ≠ 0)
    (f h : TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞))
    (p : CoordinatePoint) (inside : p ∈ protectedDiamond (conformalFrequency a)) :
    scalarFieldWaveOperator
      (licensedReadout a s (⊤ : Opens CoordinatePoint)
        (curvedLicensedMetricReceiver a s kappa Lambda coupling) []).metric
      (compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h) p =
        (massWaveNumber a) ^ 2 * compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h p := by
  rw [curved_licensed_metric_exact]
  exact compact_curved_field_equation a _ f h p (protected_diamond_subset_ball _ inside)

end AASCKleinGordon.CurvedKG
