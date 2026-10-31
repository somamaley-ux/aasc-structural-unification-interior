import KGPairedInteriorFidelity

/-! Actual prepared finite metric uses. The metric operand belongs to the
original protocol; it is not selected by a quantum ray or by its source tensor.
The quotient is by the actual field and the complete registered record. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace AASCSemanticExhaustion
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

structure KGPreparedMetricRaw {a : Parameters} (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) where
  preparation : PureVector (KGFamilyCarrier A)
  act : {H : MetricSourceProbe Ω // H ∈ D}

theorem kg_finite_metric_test_injective (Ω : Opens CoordinatePoint) :
    Function.Injective (fun H : MetricSourceProbe Ω => wickOriginalFiniteMetric H) := by
  intro H K same
  apply TestFunction.ext
  intro p
  have encoded : tensorEncode (H p)=tensorEncode (K p) := by
    funext i j
    have entry := congrArg (fun f => f (wickSpacetimeCoordinates.symm p) i j) same
    change wickFlatMetric i j+tensorEncode (H p) i j=wickFlatMetric i j+tensorEncode (K p) i j at entry
    exact add_left_cancel entry
  simpa only [tensor_decode_encode] using congrArg tensorDecode encoded

def kgPreparedMetricSame {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a)
    (x y : KGPreparedMetricRaw Ω D A) : Prop :=
  wickOriginalFiniteMetric x.act.val=wickOriginalFiniteMetric y.act.val ∧
    ∀ π,kgChartFamilyOutput a s Ω D A x.preparation π=kgChartFamilyOutput a s Ω D A y.preparation π

def kgPreparedMetricSetoid {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) : Setoid (KGPreparedMetricRaw Ω D A) where
  r := kgPreparedMetricSame s Ω D A
  iseqv := ⟨fun _ => ⟨rfl,fun _ => rfl⟩,
    fun h => ⟨h.1.symm,fun π => (h.2 π).symm⟩,
    fun h k => ⟨h.1.trans k.1,fun π => (h.2 π).trans (k.2 π)⟩⟩

abbrev KGPreparedMetricUse {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) := Quotient (kgPreparedMetricSetoid s Ω D A)

theorem kg_prepared_metric_same_iff {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) (x y : KGPreparedMetricRaw Ω D A) :
    kgPreparedMetricSame s Ω D A x y ↔
      x.act=y.act ∧ rayMap _ x.preparation=rayMap _ y.preparation := by
  constructor
  · intro h
    refine ⟨Subtype.ext (kg_finite_metric_test_injective Ω h.1),?_⟩
    exact ((kgChartRawRegisteredOrbit a s Ω D A).registered_standing_exact x.preparation y.preparation).mp
      (((kgChartRawRegisteredOrbit a s Ω D A).same_record_iff_registered x.preparation y.preparation).mp h.2)
  · rintro ⟨acts,rays⟩
    refine ⟨congrArg (fun H : {H : MetricSourceProbe Ω // H ∈ D} => wickOriginalFiniteMetric H.val) acts,?_⟩
    exact ((kgChartRawRegisteredOrbit a s Ω D A).same_record_iff_registered x.preparation y.preparation).mpr
      (((kgChartRawRegisteredOrbit a s Ω D A).registered_standing_exact x.preparation y.preparation).mpr rays)

def kgPreparedMetricAct {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) :
    KGPreparedMetricUse s Ω D A → {H : MetricSourceProbe Ω // H ∈ D} :=
  Quotient.lift KGPreparedMetricRaw.act (fun x y h => (kg_prepared_metric_same_iff s Ω D A x y).mp h |>.1)

def kgPreparedQuantum {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) :
    KGPreparedMetricUse s Ω D A → PhysicalRay (KGFamilyCarrier A) :=
  Quotient.lift (fun x => rayMap _ x.preparation)
    (fun x y h => (kg_prepared_metric_same_iff s Ω D A x y).mp h |>.2)

def kgPreparedMetricField {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) :
    KGPreparedMetricUse s Ω D A → (Spacetime → NativeRealMatrix) :=
  Quotient.lift (fun x => wickOriginalFiniteMetric x.act.val) (fun _ _ h => h.1)

def kgPreparedCompleteRecord {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) :
    KGPreparedMetricUse s Ω D A → KGChartFamilyQuestion a Ω D A → KGFamilyReadout :=
  Quotient.lift (fun x => kgChartFamilyOutput a s Ω D A x.preparation) (fun _ _ h => funext h.2)

theorem kg_prepared_metric_field_eq {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) (x : KGPreparedMetricUse s Ω D A) :
    kgPreparedMetricField s Ω D A x = wickOriginalFiniteMetric (kgPreparedMetricAct s Ω D A x).val := by
  induction x using Quotient.inductionOn with | _ x => rfl

def kgPreparedUseOfRayAct {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a)
    (H : {H : MetricSourceProbe Ω // H ∈ D}) :
    PhysicalRay (KGFamilyCarrier A) → KGPreparedMetricUse s Ω D A :=
  Quotient.lift (fun x => Quotient.mk _ (KGPreparedMetricRaw.mk x H)) (by
    intro x y same
    apply Quotient.sound
    apply (kg_prepared_metric_same_iff s Ω D A _ _).mpr
    exact ⟨rfl,(rayMap_eq_iff _ x y).mpr same⟩)

def kgPreparedUseCoordinateEquiv {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) :
    KGPreparedMetricUse s Ω D A ≃ PhysicalRay (KGFamilyCarrier A) × {H : MetricSourceProbe Ω // H ∈ D} where
  toFun x := ⟨kgPreparedQuantum s Ω D A x,kgPreparedMetricAct s Ω D A x⟩
  invFun p := kgPreparedUseOfRayAct s Ω D A p.2 p.1
  left_inv x := by
    induction x using Quotient.inductionOn with
    | _ x => cases x;rfl
  right_inv p := by
    obtain ⟨r,H⟩ := p
    induction r using Quotient.inductionOn with | _ x => rfl

theorem kg_prepared_joint_projections_faithful {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) (x y : KGPreparedMetricUse s Ω D A)
    (quantum : kgPreparedQuantum s Ω D A x=kgPreparedQuantum s Ω D A y)
    (metric : kgPreparedMetricField s Ω D A x=kgPreparedMetricField s Ω D A y) : x=y := by
  apply (kgPreparedUseCoordinateEquiv s Ω D A).injective
  apply Prod.ext quantum
  apply Subtype.ext
  apply kg_finite_metric_test_injective Ω
  simpa only [kgPreparedUseCoordinateEquiv, kg_prepared_metric_field_eq] using metric

theorem kg_prepared_quantum_does_not_erase_metric_act {a : Parameters} (s : ℝ)
    (Ω : Opens CoordinatePoint) (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a)
    (r : PhysicalRay (KGFamilyCarrier A)) (H K : {H : MetricSourceProbe Ω // H ∈ D}) (different : H ≠ K) :
    kgPreparedUseOfRayAct s Ω D A H r ≠ kgPreparedUseOfRayAct s Ω D A K r := by
  intro same
  have coords := congrArg (kgPreparedUseCoordinateEquiv s Ω D A) same
  have left := (kgPreparedUseCoordinateEquiv s Ω D A).apply_symm_apply (r,H)
  have right := (kgPreparedUseCoordinateEquiv s Ω D A).apply_symm_apply (r,K)
  exact different (congrArg Prod.snd (left.symm.trans (coords.trans right)))

end AASCKleinGordon
