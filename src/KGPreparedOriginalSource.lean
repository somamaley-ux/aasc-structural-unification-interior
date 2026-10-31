import KGPreparedMetricReferences

/-! The original structured source attachment on an act-bearing preparation.
The actual metric field is retained alongside the original full source object;
neither its tensor nor a quantum representative chooses the metric operand. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace AASCSemanticExhaustion

def kgPreparedOriginalRecord (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) :
    KGPreparedMetricUse s Ω D (kgOriginalObject a) → WickMetricPathQresp a s Ω :=
  fun x => kgOriginalQuantumRecord a s Ω (kgPreparedQuantum s Ω D (kgOriginalObject a) x)

theorem kg_prepared_original_record_raw (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (x : KGPreparedMetricRaw Ω D (kgOriginalObject a)) :
    kgPreparedOriginalRecord a s Ω D (Quotient.mk _ x)=
      Quotient.mk (wickMetricPathRoleSetoid a s Ω) ((kgRawOriginalEquiv a).symm x.preparation) := by
  change kgOriginalQuantumRecord a s Ω (rayMap _ x.preparation)=_
  have raw := kg_original_quantum_record_on_representatives a s Ω ((kgRawOriginalEquiv a).symm x.preparation)
  rw [Equiv.apply_symm_apply] at raw
  exact raw

def kgPreparedOriginalAttachment (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) :
    KGPreparedMetricUse s Ω D (kgOriginalObject a) → WickRoleQsrc a s Ω :=
  fun x => kgInteriorSourceAttachment a s Ω (kgPreparedOriginalRecord a s Ω D x)

def kgPreparedOriginalSourceLedger (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) :
    KGPreparedMetricUse s Ω D (kgOriginalObject a) → WickSourceLedgerValue Ω :=
  fun x => kgInteriorSourceLedger a s Ω (kgPreparedOriginalRecord a s Ω D x)

def kgPreparedOriginalMetricRole (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) :
    KGPreparedMetricUse s Ω D (kgOriginalObject a) →
      (Spacetime → NativeRealMatrix) × WickRoleQsrc a s Ω :=
  fun x => ⟨kgPreparedMetricField s Ω D (kgOriginalObject a) x,kgPreparedOriginalAttachment a s Ω D x⟩

theorem kg_prepared_original_attachment_raw (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (x : KGPreparedMetricRaw Ω D (kgOriginalObject a)) :
    kgPreparedOriginalAttachment a s Ω D (Quotient.mk _ x)=
      wickRolePiA a s Ω (wickOriginalRoleSource a s Ω ((kgRawOriginalEquiv a).symm x.preparation)) := by
  unfold kgPreparedOriginalAttachment
  rw [kg_prepared_original_record_raw]
  rfl

theorem kg_prepared_original_source_ledger_exact (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (x : KGPreparedMetricUse s Ω D (kgOriginalObject a)) :
    kgPreparedOriginalSourceLedger a s Ω D x=wickOriginalSourceLedgerValue Ω :=
  kg_interior_source_ledger_exact a s Ω (kgPreparedOriginalRecord a s Ω D x)

theorem kg_prepared_original_all_first_tests (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (x : KGPreparedMetricUse s Ω D (kgOriginalObject a))
    (H : MetricSourceProbe Ω) :
    (1/2 : ℝ)*metricSourcePairing (wickRoleQg a s Ω (kgPreparedOriginalAttachment a s Ω D x)) H=
      kgInteriorFirstResponse a s Ω (kgPreparedOriginalRecord a s Ω D x) H := by
  rw [kgPreparedOriginalAttachment,kg_interior_source_attachment_tensor]
  exact kg_interior_metric_half_pairing a s Ω (kgPreparedOriginalRecord a s Ω D x) H

theorem kg_prepared_original_pair_faithful (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (x y : KGPreparedMetricUse s Ω D (kgOriginalObject a))
    (metric : kgPreparedOriginalMetricRole a s Ω D x=kgPreparedOriginalMetricRole a s Ω D y)
    (quantum : kgPreparedQuantum s Ω D (kgOriginalObject a) x=
      kgPreparedQuantum s Ω D (kgOriginalObject a) y) : x=y :=
  kg_prepared_joint_projections_faithful s Ω D (kgOriginalObject a) x y quantum (congrArg Prod.fst metric)

end AASCKleinGordon
