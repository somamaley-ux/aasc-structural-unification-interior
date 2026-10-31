import KGOriginalMetricActFidelity

/-! A receiving-region change reuses the original raw preparation and its
proved original equivalence. Compact tests extend as the same global test.
No arbitrary restriction of a compact test or new global section is asserted. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace AASCSemanticExhaustion

def kgInteriorRebase (a : Parameters) (s : ℝ) (Ω V : Opens CoordinatePoint) :
    WickMetricPathQresp a s Ω → WickMetricPathQresp a s V :=
  Quotient.map id (fun u v same => (wick_metric_path_record_iff_ray a s V u v).mpr
    ((wick_metric_path_record_iff_ray a s Ω u v).mp same))

theorem kg_interior_rebase_quantum (a : Parameters) (s : ℝ) (Ω V : Opens CoordinatePoint)
    (x : WickMetricPathQresp a s Ω) :
    kgInteriorQuantum a s V (kgInteriorRebase a s Ω V x)=kgInteriorQuantum a s Ω x := by
  induction x using Quotient.inductionOn with | _ u => rfl

theorem kg_interior_rebase_first (a : Parameters) (s : ℝ) (Ω V : Opens CoordinatePoint)
    (x : WickMetricPathQresp a s Ω) :
    kgInteriorFirstResponse a s V (kgInteriorRebase a s Ω V x)=kgInteriorFirstResponseAt a s Ω V x := by
  induction x using Quotient.inductionOn with | _ u => rfl

theorem kg_interior_rebase_source (a : Parameters) (s : ℝ) (Ω V : Opens CoordinatePoint)
    (x : WickMetricPathQresp a s Ω) :
    kgInteriorMetricSource a s V (kgInteriorRebase a s Ω V x)=kgInteriorMetricSourceAt a s Ω V x := by
  induction x using Quotient.inductionOn with | _ u => rfl

theorem kg_interior_regional_complete (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    {V W : Opens CoordinatePoint} (h : V ≤ W) (x : WickMetricPathQresp a s Ω)
    (π : WickMetricPathRoleProtocol V) :
    wickIdentifiedMetricPathRecordReadout a s W (kgInteriorRebase a s Ω W x)
      (kgExtendOriginalProtocol h π)=
      wickIdentifiedMetricPathRecordReadout a s V (kgInteriorRebase a s Ω V x) π := by
  induction x using Quotient.inductionOn with
  | _ u => exact kg_complete_original_regional_output a s h u π

theorem kg_interior_regional_first (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    {V W : Opens CoordinatePoint} (h : V ≤ W) (x : WickMetricPathQresp a s Ω)
    (H : MetricSourceProbe V) :
    kgInteriorFirstResponseAt a s Ω W x (kgExtendMetricProbe h H)=
      kgInteriorFirstResponseAt a s Ω V x H := by
  have records := kg_interior_regional_complete a s Ω h x
    (.original (.metric (.first (wickKGIdentityAct H))))
  change wickIdentifiedMetricPathRecordReadout a s W (kgInteriorRebase a s Ω W x)
      (.original (.metric (.first (wickKGIdentityAct (kgExtendMetricProbe h H)))))=
    wickIdentifiedMetricPathRecordReadout a s V (kgInteriorRebase a s Ω V x)
      (.original (.metric (.first (wickKGIdentityAct H)))) at records
  rw [kg_interior_first_response_is_original,kg_interior_first_response_is_original,
    kg_interior_rebase_first,kg_interior_rebase_first] at records
  exact WickKGOriginalReadout.first.inj (WickRoleReadout.metric.inj records)

def kgMetricSourceRestriction {V W : Opens CoordinatePoint} (h : V ≤ W)
    (T : SymmetricSourceComponents W) : SymmetricSourceComponents V :=
  representedMetricSource ((kgSourceHalfResponse T).comp (kgExtendMetricProbeCLM h))

theorem kg_metric_source_restriction_all_tests {V W : Opens CoordinatePoint} (h : V ≤ W)
    (T : SymmetricSourceComponents W) (H : MetricSourceProbe V) :
    (1/2 : ℝ)*metricSourcePairing (kgMetricSourceRestriction h T) H=
      (1/2 : ℝ)*metricSourcePairing T (kgExtendMetricProbe h H) :=
  (constructed_metric_source_represents _ H).trans (kg_source_half_response_apply T _)

theorem kg_interior_regional_source (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    {V W : Opens CoordinatePoint} (h : V ≤ W) (x : WickMetricPathQresp a s Ω) :
    kgMetricSourceRestriction h (kgInteriorMetricSourceAt a s Ω W x)=
      kgInteriorMetricSourceAt a s Ω V x := by
  have functionals : (kgInteriorFirstResponseAt a s Ω W x).comp (kgExtendMetricProbeCLM h)=
      kgInteriorFirstResponseAt a s Ω V x := by
    ext H
    exact kg_interior_regional_first a s Ω h x H
  rw [kgMetricSourceRestriction,kg_interior_half_response_at,functionals]
  exact (constructed_metric_source_unique _ _ (kg_interior_at_half_pairing a s Ω V x)).symm

theorem kg_interior_rebase_identity (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (x : WickMetricPathQresp a s Ω) : kgInteriorRebase a s Ω Ω x=x := by
  induction x using Quotient.inductionOn with | _ u => rfl

theorem kg_interior_rebase_comp (a : Parameters) (s : ℝ) (Ω V W : Opens CoordinatePoint)
    (x : WickMetricPathQresp a s Ω) :
    kgInteriorRebase a s V W (kgInteriorRebase a s Ω V x)=kgInteriorRebase a s Ω W x := by
  induction x using Quotient.inductionOn with | _ u => rfl

end AASCKleinGordon
