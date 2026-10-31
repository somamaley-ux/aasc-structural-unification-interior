import KGOriginalQuantumRecord
import KGRawQuantumOperations

noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open scoped TensorProduct
open KGQuantum TopologicalSpace AASCSemanticExhaustion

theorem kg_raw_transport_scalar_orbits {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (U : E ≃ₗᵢ[ℂ] E) (x x' y y' : PureVector E)
    (hx : PureVector.ScalarRel x x') (hy : PureVector.ScalarRel y y') :
    transitionProbability x (PureVector.mapUnitary U y) =
      transitionProbability x' (PureVector.mapUnitary U y') := by
  obtain ⟨c,hc,hx⟩ := hx
  obtain ⟨d,hd,hy⟩ := hy
  have ex : PureVector.smul c hc x=x' := Subtype.ext hx
  have ey : PureVector.smul d hd y=y' := Subtype.ext hy
  have moved : PureVector.mapUnitary U (PureVector.smul d hd y) =
      PureVector.smul d hd (PureVector.mapUnitary U y) := Subtype.ext (U.map_smul d y.val)
  rw [← ex,← ey,moved]
  exact (transitionProbability_smul c d hc hd x (PureVector.mapUnitary U y)).symm

theorem kg_raw_transport_normalizations {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (U : E ≃ₗᵢ[ℂ] E) (x x' y y' : PureVector E)
    (hx : ∃ (c : ℂ) (hc : c ≠ 0), x'=PureVector.smul c hc x)
    (hy : ∃ (d : ℂ) (hd : d ≠ 0), y'=PureVector.smul d hd y)
    (r : ℝ) (comparison : transitionProbability x' (PureVector.mapUnitary U y')=r) :
    transitionProbability x (PureVector.mapUnitary U y) = r := by
  obtain ⟨c,hc,hx⟩ := hx
  obtain ⟨d,hd,hy⟩ := hy
  exact (kg_raw_transport_scalar_orbits U x x' y y'
    ⟨c,hc,(congrArg Subtype.val hx).symm⟩
    ⟨d,hd,(congrArg Subtype.val hy).symm⟩).trans comparison

/-- Restriction of the actual original representation to its proved invariant
core. No arbitrary completed-Hilbert unitary is asserted to preserve it. -/
def kgCorePoincareIsometry (a : Parameters) (q : ProperPoincareTransform) :
    fockCoreDomain a ≃ₗᵢ[ℂ] fockCoreDomain a where
  toFun x := ⟨originalFockPoincareRepresentation a q x.val,
    originalFockPoincareRepresentation_preserves_domain a q x⟩
  invFun x := ⟨originalFockPoincareRepresentation a q⁻¹ x.val,
    originalFockPoincareRepresentation_preserves_domain a q⁻¹ x⟩
  left_inv x := by
    apply Subtype.ext
    change (originalFockPoincareRepresentation a q⁻¹ *
      originalFockPoincareRepresentation a q) x.val=x.val
    rw [← map_mul,inv_mul_cancel,map_one]
    rfl
  right_inv x := by
    apply Subtype.ext
    change (originalFockPoincareRepresentation a q *
      originalFockPoincareRepresentation a q⁻¹) x.val=x.val
    rw [← map_mul,mul_inv_cancel,map_one]
    rfl
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c x := by apply Subtype.ext; exact map_smul _ _ _
  norm_map' x := (originalFockPoincareRepresentation a q).norm_map x.val

theorem kg_raw_original_actual_continuation (a : Parameters) (q : ProperPoincareTransform)
    (u : WickNonzeroCore) :
    PureVector.mapUnitary (kgCorePoincareIsometry a q) (kgRawOriginalEquiv a u) =
      kgRawOriginalEquiv a (wickPoincareNonzeroCore a q.left.toAdd q.right u) := by
  apply Subtype.ext
  apply Subtype.ext
  exact fockPoincare_intertwines_original_core a q.left.toAdd q.right u.val

theorem kg_raw_normalized_original_probability (a : Parameters)
    (u v : WickNonzeroCore) (g : ProperPoincareTransform) :
    transitionProbability
      (kgRawOriginalEquiv a (originalWickUnitNonzeroRepresentative a v))
      (PureVector.mapUnitary (kgCorePoincareIsometry a g)
        (kgRawOriginalEquiv a (originalWickUnitNonzeroRepresentative a u))) =
      wickOriginalRoleComparison a u v g := by
  have nu : ‖(kgRawOriginalEquiv a (originalWickUnitNonzeroRepresentative a u)).val‖=1 :=
    original_wick_unit_representative_norm a u.val u.property
  have nv : ‖(kgRawOriginalEquiv a (originalWickUnitNonzeroRepresentative a v)).val‖=1 :=
    original_wick_unit_representative_norm a v.val v.property
  simp only [transitionProbability,PureVector.coe_mapUnitary,
    (kgCorePoincareIsometry a g).norm_map,nv,nu,one_pow,one_mul,div_one]
  rfl

/-- The raw quantum probability is exactly the original Born/Poincare
comparison, including for unnormalized representatives. -/
theorem kg_raw_original_normalization_scalar (a : Parameters) (u : WickNonzeroCore) :
    ∃ (c : ℂ) (hc : c ≠ 0),
      kgRawOriginalEquiv a (originalWickUnitNonzeroRepresentative a u) =
        PureVector.smul c hc (kgRawOriginalEquiv a u) := by
  have same : wickCoreRaySetoid.r u (originalWickUnitNonzeroRepresentative a u) :=
    Quotient.exact (original_wick_unit_representative_same_ray a u).symm
  obtain ⟨c,hc,identity⟩ := same
  refine ⟨c,hc,Subtype.ext ?_⟩
  exact (congrArg (fockCoreDomainEquiv a) identity).trans
    ((fockCoreDomainEquiv a).map_smul c u.val)

section RawComparisonMatching
attribute [local irreducible] kgRawOriginalEquiv kgCorePoincareIsometry PureVector.mapUnitary
  transitionProbability wickOriginalRoleComparison

set_option diagnostics true in
theorem kg_raw_probability_is_original_comparison (a : Parameters)
    (u v : WickNonzeroCore) (g : ProperPoincareTransform) :
    transitionProbability (kgRawOriginalEquiv a v)
      (PureVector.mapUnitary (kgCorePoincareIsometry a g) (kgRawOriginalEquiv a u)) =
      wickOriginalRoleComparison a u v g := by
  exact @kg_raw_transport_normalizations (fockCoreDomain a)
    (inferInstance : NormedAddCommGroup (fockCoreDomain a))
    (inferInstance : InnerProductSpace ℂ (fockCoreDomain a))
    (kgCorePoincareIsometry a g)
    (kgRawOriginalEquiv a v)
    (kgRawOriginalEquiv a (originalWickUnitNonzeroRepresentative a v))
    (kgRawOriginalEquiv a u)
    (kgRawOriginalEquiv a (originalWickUnitNonzeroRepresentative a u))
    (kg_raw_original_normalization_scalar a v)
    (kg_raw_original_normalization_scalar a u) (wickOriginalRoleComparison a u v g)
    (kg_raw_normalized_original_probability a u v g)

end RawComparisonMatching

section TensorComparisons
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

def kgComparisonPoincare (a : Parameters) (q : ProperPoincareTransform) :
    (A : KGComparisonObject) → KGComparisonCarrier a A ≃ₗᵢ[ℂ] KGComparisonCarrier a A
  | .unit => LinearIsometryEquiv.refl ℂ ℂ
  | .kg => kgCorePoincareIsometry a q
  | .tensor A B => TensorProduct.congrIsometry
      (kgComparisonPoincare a q A) (kgComparisonPoincare a q B)

theorem kg_comparison_continuation_one (a : Parameters) (A : KGComparisonObject)
    (x : KGComparisonCarrier a A) : kgComparisonPoincare a 1 A x=x := by
  induction A with
  | unit => rfl
  | kg =>
    apply Subtype.ext
    change originalFockPoincareRepresentation a 1 x.val=x.val
    rw [map_one]
    rfl
  | tensor A B hA hB =>
    induction x using TensorProduct.induction_on with
    | zero => exact map_zero _
    | tmul x y =>
      change (kgComparisonPoincare a 1 A x) ⊗ₜ[ℂ] (kgComparisonPoincare a 1 B y) = x ⊗ₜ[ℂ] y
      exact congrArg₂ (fun v w => v ⊗ₜ[ℂ] w) (hA x) (hB y)
    | add x y hx hy => rw [map_add,hx,hy]

theorem kg_comparison_continuation_mul (a : Parameters) (q r : ProperPoincareTransform)
    (A : KGComparisonObject) (x : KGComparisonCarrier a A) :
    kgComparisonPoincare a (q*r) A x =
      kgComparisonPoincare a q A (kgComparisonPoincare a r A x) := by
  induction A with
  | unit => rfl
  | kg =>
    apply Subtype.ext
    change originalFockPoincareRepresentation a (q*r) x.val =
      originalFockPoincareRepresentation a q (originalFockPoincareRepresentation a r x.val)
    rw [map_mul]
    rfl
  | tensor A B hA hB =>
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      change (kgComparisonPoincare a (q*r) A x) ⊗ₜ[ℂ] (kgComparisonPoincare a (q*r) B y) =
        (kgComparisonPoincare a q A (kgComparisonPoincare a r A x)) ⊗ₜ[ℂ]
          (kgComparisonPoincare a q B (kgComparisonPoincare a r B y))
      exact congrArg₂ (fun v w => v ⊗ₜ[ℂ] w) (hA x) (hB y)
    | add x y hx hy => simp only [map_add,hx,hy]

/-- Lawful Poincare arrows transport the continuation parameter by conjugacy.
No assertion that boosts commute with a fixed time subgroup is made. -/
theorem kg_comparison_continuation_conjugate (a : Parameters)
    (g q : ProperPoincareTransform) (A : KGComparisonObject) (x : KGComparisonCarrier a A) :
    kgComparisonPoincare a (g*q*g⁻¹) A (kgComparisonPoincare a g A x) =
      kgComparisonPoincare a g A (kgComparisonPoincare a q A x) := by
  rw [← kg_comparison_continuation_mul]
  have equal : (g*q*g⁻¹)*g=g*q := by group
  rw [equal,kg_comparison_continuation_mul]

theorem kg_comparison_continuation_weights (a : Parameters) (q : ProperPoincareTransform)
    (A : KGComparisonObject) (x y : PureVector (KGComparisonCarrier a A)) :
    transitionProbability (PureVector.mapUnitary (kgComparisonPoincare a q A) x)
      (PureVector.mapUnitary (kgComparisonPoincare a q A) y) = transitionProbability x y :=
  transitionProbability_mapUnitary _ x y

theorem kg_comparison_continuation_monoidal (a : Parameters) (q : ProperPoincareTransform)
    (A B : KGComparisonObject) (x : PureVector (KGComparisonCarrier a A))
    (y : PureVector (KGComparisonCarrier a B)) :
    PureVector.mapUnitary (kgComparisonPoincare a q (.tensor A B)) (kgRawTensor x y) =
      kgRawTensor (PureVector.mapUnitary (kgComparisonPoincare a q A) x)
        (PureVector.mapUnitary (kgComparisonPoincare a q B) y) := by
  apply Subtype.ext
  rfl

end TensorComparisons

def kgOriginalRecordContinuation (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (q : ProperPoincareTransform) : WickMetricPathQresp a s Ω → WickMetricPathQresp a s Ω :=
  Quotient.map (wickPoincareNonzeroCore a q.left.toAdd q.right) (by
    intro u v same
    apply (wick_metric_path_record_iff_ray a s Ω _ _).mpr
    obtain ⟨c,hc,h⟩ := (wick_metric_path_record_iff_ray a s Ω u v).mp same
    refine ⟨c,hc,?_⟩
    exact (congrArg (corePoincare a q.left.toAdd q.right) h).trans
      ((corePoincare a q.left.toAdd q.right).map_smul c u.val))

/-- Actual original continuation is compared at raw representatives first. -/
theorem kg_original_quantum_record_continuation (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (q : ProperPoincareTransform)
    (r : PhysicalRay (fockCoreDomain a)) :
    kgOriginalQuantumRecord a s Ω (unitaryRayMap (kgCorePoincareIsometry a q) r) =
      kgOriginalRecordContinuation a s Ω q (kgOriginalQuantumRecord a s Ω r) := by
  induction r using Quotient.inductionOn with
  | _ x =>
    let u := (kgRawOriginalEquiv a).symm x
    have back : kgRawOriginalEquiv a u=x := (kgRawOriginalEquiv a).apply_symm_apply x
    rw [← back]
    change kgOriginalQuantumRecord a s Ω
      (rayMap _ (PureVector.mapUnitary (kgCorePoincareIsometry a q) (kgRawOriginalEquiv a u))) =
      kgOriginalRecordContinuation a s Ω q
        (kgOriginalQuantumRecord a s Ω (rayMap _ (kgRawOriginalEquiv a u)))
    rw [kg_raw_original_actual_continuation,
      kg_original_quantum_record_on_representatives,kg_original_quantum_record_on_representatives]
    rfl

theorem kg_original_quantum_ray_continuation (a : Parameters) (q : ProperPoincareTransform)
    (r : PhysicalRay (fockCoreDomain a)) :
    kgOriginalQuantumToRay a (unitaryRayMap (kgCorePoincareIsometry a q) r) =
      wickPoincareRayAction a q.left.toAdd q.right (kgOriginalQuantumToRay a r) := by
  induction r using Quotient.inductionOn with
  | _ x =>
    let u := (kgRawOriginalEquiv a).symm x
    have back : kgRawOriginalEquiv a u=x := (kgRawOriginalEquiv a).apply_symm_apply x
    rw [← back]
    change kgOriginalQuantumToRay a
      (rayMap _ (PureVector.mapUnitary (kgCorePoincareIsometry a q) (kgRawOriginalEquiv a u))) =
      wickPoincareRayAction a q.left.toAdd q.right
        (kgOriginalQuantumToRay a (rayMap _ (kgRawOriginalEquiv a u)))
    rw [kg_raw_original_actual_continuation]
    change Quotient.mk wickCoreRaySetoid
      ((kgRawOriginalEquiv a).symm (kgRawOriginalEquiv a
        (wickPoincareNonzeroCore a q.left.toAdd q.right u))) =
      Quotient.mk wickCoreRaySetoid (wickPoincareNonzeroCore a q.left.toAdd q.right
        ((kgRawOriginalEquiv a).symm (kgRawOriginalEquiv a u)))
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]

/-- Covariance transports the complete actual question and finite admission
chart; it is stronger than the fixed-question state continuation square. -/
theorem kg_original_quantum_complete_covariant_source (a : Parameters) (s : ℝ)
    (q : ProperPoincareTransform) (Ω : Opens CoordinatePoint)
    (r : PhysicalRay (fockCoreDomain a)) (π : WickMetricPathRoleProtocol Ω) :
    wickChartMetricPathRayOutput a s (wickAffineMetricRegion q.left.toAdd q.right Ω)
      (wickTransportedMetricDomain q.left.toAdd q.right Ω)
      (kgOriginalQuantumToRay a (unitaryRayMap (kgCorePoincareIsometry a q) r))
      (wickChartMetricPathProtocolPoincare a q (wickOriginalMetricPathInChart π)) =
      wickIdentifiedMetricPathRecordReadout a s Ω (kgOriginalQuantumRecord a s Ω r) π := by
  rw [kg_original_quantum_ray_continuation,kg_original_quantum_source_square]
  exact wick_metric_path_covariant_original_source_square a s q Ω (kgOriginalQuantumToRay a r) π

end AASCKleinGordon
