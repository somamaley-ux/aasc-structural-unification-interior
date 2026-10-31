import KGOriginalInteriorProjections

/-! Receiving regions and admission charts are indexed independently of the
original content carrier. The original equivalence is proved to preserve each
actual receiver, rather than declaring a fixed admission box invariant. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace AASCSemanticExhaustion

def kgInteriorOriginalRay (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    WickMetricPathQresp a s Ω → Quotient wickCoreRaySetoid :=
  Quotient.map id (fun u v same => (wick_metric_path_record_iff_ray a s Ω u v).mp same)

def kgInteriorFirstResponseAt (a : Parameters) (s : ℝ) (Ω V : Opens CoordinatePoint) :
    WickMetricPathQresp a s Ω → (MetricSourceProbe V →L[ℝ] ℝ) :=
  Quotient.lift (fun u => (wickOriginalRoleSource a s V u).attachment.functional) (by
    intro u v same
    exact (wick_full_role_implies_source_agreement
      (wickOriginalRoleSource a s V u) (wickOriginalRoleSource a s V v)
      (wick_role_same_ray_entire_signature a s V u v
        ((wick_metric_path_record_iff_ray a s Ω u v).mp same))).2.2.1)

def kgInteriorMetricSourceAt (a : Parameters) (s : ℝ) (Ω V : Opens CoordinatePoint) :
    WickMetricPathQresp a s Ω → SymmetricSourceComponents V :=
  Quotient.lift (fun u => (wickOriginalRoleSource a s V u).attachment.represented) (by
    intro u v same
    exact (wick_full_role_implies_source_agreement
      (wickOriginalRoleSource a s V u) (wickOriginalRoleSource a s V v)
      (wick_role_same_ray_entire_signature a s V u v
        ((wick_metric_path_record_iff_ray a s Ω u v).mp same))).2.2.2.1)

def kgInteriorChartReadout (a : Parameters) (s : ℝ) (Ω V : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe V)) :
    WickMetricPathQresp a s Ω → WickChartMetricPathProtocol V D → WickRoleReadout :=
  Quotient.lift (wickChartMetricPathOutput a s V D) (by
    intro u v same
    funext π
    exact wick_chart_metric_path_output_same_ray a s V D u v
      ((wick_metric_path_record_iff_ray a s Ω u v).mp same) π)

theorem kg_interior_first_response_at_original_ray (a : Parameters) (s : ℝ)
    (Ω V : Opens CoordinatePoint) (x : WickMetricPathQresp a s Ω) :
    kgInteriorFirstResponseAt a s Ω V x=
      originalWickRayMetricResponse a s V (kgInteriorOriginalRay a s Ω x) := by
  induction x using Quotient.inductionOn with
  | _ u =>
    exact (wickOriginalRoleSource a s V u).attachment.same_original_source.trans
      (original_wick_ray_source_is_actual_unit_response a s V u).symm

theorem kg_interior_same_first_receiver (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (x : WickMetricPathQresp a s Ω) :
    kgInteriorFirstResponseAt a s Ω Ω x=kgInteriorFirstResponse a s Ω x := by
  induction x using Quotient.inductionOn with | _ u => rfl

theorem kg_interior_same_metric_receiver (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (x : WickMetricPathQresp a s Ω) :
    kgInteriorMetricSourceAt a s Ω Ω x=kgInteriorMetricSource a s Ω x := by
  induction x using Quotient.inductionOn with | _ u => rfl

theorem kg_interior_same_original_chart (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (x : WickMetricPathQresp a s Ω)
    (π : WickMetricPathRoleProtocol Ω) :
    kgInteriorChartReadout a s Ω Ω (wickOriginalMetricNeighborhood Ω) x
      (wickOriginalMetricPathInChart π)=wickIdentifiedMetricPathRecordReadout a s Ω x π := by
  induction x using Quotient.inductionOn with
  | _ u => exact wick_original_metric_path_chart_exact a s Ω u π

theorem kg_interior_at_half_pairing (a : Parameters) (s : ℝ)
    (Ω V : Opens CoordinatePoint) (x : WickMetricPathQresp a s Ω) (H : MetricSourceProbe V) :
    (1/2 : ℝ)*metricSourcePairing (kgInteriorMetricSourceAt a s Ω V x) H=
      kgInteriorFirstResponseAt a s Ω V x H := by
  induction x using Quotient.inductionOn with
  | _ u => exact (wickOriginalRoleSource a s V u).attachment.half_pairing H

theorem kg_interior_at_metric_faithful (a : Parameters) (s : ℝ)
    (Ω V : Opens CoordinatePoint) (x y : WickMetricPathQresp a s Ω) :
    kgInteriorMetricSourceAt a s Ω V x=kgInteriorMetricSourceAt a s Ω V y ↔
      ∀ H : MetricSourceProbe V,
        kgInteriorFirstResponseAt a s Ω V x H=kgInteriorFirstResponseAt a s Ω V y H := by
  constructor
  · intro same H
    exact (kg_interior_at_half_pairing a s Ω V x H).symm.trans
      ((congrArg (fun T => (1/2 : ℝ)*metricSourcePairing T H) same).trans
        (kg_interior_at_half_pairing a s Ω V y H))
  · intro same
    have functionals : kgInteriorFirstResponseAt a s Ω V x=kgInteriorFirstResponseAt a s Ω V y := by
      ext H
      exact same H
    exact (constructed_metric_source_unique _ _ (kg_interior_at_half_pairing a s Ω V x)).trans
      ((congrArg representedMetricSource functionals).trans
        (constructed_metric_source_unique _ _ (kg_interior_at_half_pairing a s Ω V y)).symm)

theorem kg_interior_chart_incident_graph (a : Parameters) (s : ℝ)
    (Ω V : Opens CoordinatePoint) (D : Set (MetricSourceProbe V))
    (x : WickMetricPathQresp a s Ω) (H : MetricSourceProbe V) (z : ℝ) :
    (∃ π : WickChartMetricPathProtocol V D,wickChartMetricPathMetInc H π ∧
      kgInteriorChartReadout a s Ω V D x π=.metric (.first z)) ↔
      kgInteriorFirstResponseAt a s Ω V x H=z := by
  induction x using Quotient.inductionOn with
  | _ u =>
    change wickChartMetricPathMetResp a s V D u H z ↔
      (wickOriginalRoleSource a s V u).attachment.functional H=z
    have source := (wickOriginalRoleSource a s V u).attachment.same_original_source
    change (wickOriginalRoleSource a s V u).attachment.functional=
      originalWickNativeRealMetricResponse a s (originalWickUnitRepresentative a u.val) V at source
    rw [wick_complete_chart_metric_response_graph,source]

end AASCKleinGordon
