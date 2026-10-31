import EHKGOriginalMetricReceiver

/-! The constraint-first attachment is obtained from the original task's
proved necessity/licensing chain. No causal, metric or scalar-output property
is used to infer those upstream roles. The concrete operand is then proved
qualified/admitted in that existing original task. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing AASC.KernelReference
open AASCMetricityOriginalAssembly AASCMetricityLicensingConstruction
open scoped Topology
namespace AASCKleinGordon.CurvedKG

theorem curved_original_task_kernel_licensing (a : Parameters) (s kappa Lambda : ℝ)
    (coupling : kappa ≠ 0) :
    let D := originalMetricTask a s (⊤ : Opens CoordinatePoint) kappa Lambda
    AASC.Instances.KernelPaper.Manuscript.DerivedKernelRoles
      (ObjecthoodNecessity.canonicalRegime (originalIncidence D)) ∧
    AASCAMetricMetricUse.AMetricLicensingDiscipline ∧ FiveLicensingConclusions D ∧
      constructedLicensing D (curvedOriginalMetricHistory a)
        (originalMetricUseMeaning a s (⊤ : Opens CoordinatePoint) kappa Lambda) := by
  have upstream := current_metric_use_constructs_kernel_and_canonical_license
    a s (⊤ : Opens CoordinatePoint) kappa Lambda coupling
  exact ⟨upstream.1, upstream.2.1, upstream.2.2.1, upstream.2.2.2 (curvedOriginalMetricHistory a)⟩

theorem curved_original_history_qualified (a : Parameters) (s : ℝ) :
    rawHistoryQualified a s (⊤ : Opens CoordinatePoint) (curvedOriginalMetricHistory a) :=
  raw_history_qualified a s _ _

theorem curved_original_finite_eh_use_admitted (a : Parameters) (kappa Lambda : ℝ)
    (coupling : kappa ≠ 0) :
    OriginalEHFiniteUseDomain kappa Lambda wickNativeFlatMetric (conformalOperand (conformalFrequency a)) :=
  original_eh_original_act_admitted kappa Lambda coupling _ (protected_same_eh_nonflat a).2.1

end AASCKleinGordon.CurvedKG
