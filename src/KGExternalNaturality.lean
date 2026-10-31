import KGStandingOperations

/-! External Poincare arrows conjugate continuation parameters and act on
internal comparisons by the actual U_B S U_A^{-1} formula. Their equality to S
is proved from the declared intertwining law, not asserted for arbitrary maps. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 CategoryTheory TopologicalSpace AASCSemanticExhaustion
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

def kgFrameConjugateIsometry {a : Parameters} (g : ProperPoincareTransform)
    {A B : KGFamilyObject a} (f : A ⟶ B) : KGFamilyCarrier A ≃ₗᵢ[ℂ] KGFamilyCarrier B :=
  ((kgComparisonPoincare a g A.shape).symm.trans f.isometry).trans
    (kgComparisonPoincare a g B.shape)

theorem kg_frame_conjugate_isometry {a : Parameters} (g : ProperPoincareTransform)
    {A B : KGFamilyObject a} (f : A ⟶ B) : kgFrameConjugateIsometry g f=f.isometry := by
  ext x
  have h := f.intertwines g ((kgComparisonPoincare a g A.shape).symm x)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

def kgFrameArrow {a : Parameters} (g : ProperPoincareTransform)
    {A B : KGFamilyObject a} (f : A ⟶ B) : A ⟶ B where
  isometry := kgFrameConjugateIsometry g f
  intertwines q x := by
    rw [kg_frame_conjugate_isometry]
    exact f.intertwines q x

theorem kg_frame_arrow_eq {a : Parameters} (g : ProperPoincareTransform)
    {A B : KGFamilyObject a} (f : A ⟶ B) : kgFrameArrow g f=f :=
  kg_internal_arrow_ext (kg_frame_conjugate_isometry g f)

def kgFrameComparisonFunctor (a : Parameters) (g : ProperPoincareTransform) :
    KGFamilyObject a ⥤ KGFamilyObject a where
  obj A := A
  map f := kgFrameArrow g f
  map_id A := kg_frame_arrow_eq g (𝟙 A)
  map_comp f h := by rw [kg_frame_arrow_eq,kg_frame_arrow_eq,kg_frame_arrow_eq]

theorem kg_frame_comparison_functor_eq (a : Parameters) (g : ProperPoincareTransform) :
    kgFrameComparisonFunctor a g=𝟭 (KGFamilyObject a) :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun A B f => by
    change kgFrameArrow g f=(𝟙 A) ≫ f ≫ (𝟙 B)
    rw [kg_frame_arrow_eq,Category.id_comp,Category.comp_id])

instance kgFrameComparisonMonoidal (a : Parameters) (g : ProperPoincareTransform) :
    (kgFrameComparisonFunctor a g).Monoidal := by
  rw [kg_frame_comparison_functor_eq]
  infer_instance

instance kgFrameComparisonBraided (a : Parameters) (g : ProperPoincareTransform) :
    (kgFrameComparisonFunctor a g).LaxBraided := by
  rw [kg_frame_comparison_functor_eq]
  infer_instance

theorem kg_frame_comparison_tensor {a : Parameters} (g : ProperPoincareTransform)
    {A B C D : KGFamilyObject a} (f : A ⟶ B) (h : C ⟶ D) :
    kgFrameArrow g (kgInternalTensor f h)=kgInternalTensor (kgFrameArrow g f) (kgFrameArrow g h) := by
  rw [kg_frame_arrow_eq,kg_frame_arrow_eq,kg_frame_arrow_eq]

theorem kg_raw_external_continuation (a : Parameters) (g q : ProperPoincareTransform)
    (A : KGFamilyObject a) (x : PureVector (KGFamilyCarrier A)) :
    kgFamilyFlow (g*q*g⁻¹) (kgFamilyFlow g x)=kgFamilyFlow g (kgFamilyFlow q x) :=
  Subtype.ext (kg_comparison_continuation_conjugate a g q A.shape x.val)

theorem kg_standing_external_continuation (a : Parameters) (g q : ProperPoincareTransform)
    (A : KGFamilyObject a) (r : PhysicalRay (KGFamilyCarrier A)) :
    kgStandingFlow (g*q*g⁻¹) A (kgStandingFlow g A r)=kgStandingFlow g A (kgStandingFlow q A r) := by
  induction r using Quotient.inductionOn with
  | _ x => exact congrArg (rayMap _) (kg_raw_external_continuation a g q A x)

def kgFrameOperator {a : Parameters} (g : ProperPoincareTransform) (A : KGFamilyObject a)
    (S : KGFamilyCarrier A →ₗ[ℂ] KGFamilyCarrier A) : KGFamilyCarrier A →ₗ[ℂ] KGFamilyCarrier A :=
  (kgComparisonPoincare a g A.shape).toLinearMap.comp
    (S.comp (kgComparisonPoincare a g A.shape).symm.toLinearMap)

theorem kg_frame_operator_add {a : Parameters} (g : ProperPoincareTransform) (A : KGFamilyObject a)
    (S T : KGFamilyCarrier A →ₗ[ℂ] KGFamilyCarrier A) :
    kgFrameOperator g A (S+T)=kgFrameOperator g A S+kgFrameOperator g A T := by
  ext x
  exact map_add (kgComparisonPoincare a g A.shape) _ _

theorem kg_frame_operator_comp {a : Parameters} (g : ProperPoincareTransform) (A : KGFamilyObject a)
    (S T : KGFamilyCarrier A →ₗ[ℂ] KGFamilyCarrier A) :
    kgFrameOperator g A (S.comp T)=(kgFrameOperator g A S).comp (kgFrameOperator g A T) := by
  ext x
  change kgComparisonPoincare a g A.shape (S (T ((kgComparisonPoincare a g A.shape).symm x)))=
    kgComparisonPoincare a g A.shape (S ((kgComparisonPoincare a g A.shape).symm
      (kgComparisonPoincare a g A.shape (T ((kgComparisonPoincare a g A.shape).symm x)))))
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem kg_frame_operator_identity {a : Parameters} (g : ProperPoincareTransform) (A : KGFamilyObject a) :
    kgFrameOperator g A LinearMap.id=LinearMap.id := by
  ext x
  exact (kgComparisonPoincare a g A.shape).apply_symm_apply x

theorem kg_frame_operator_scalar {a : Parameters} (g : ProperPoincareTransform) (A : KGFamilyObject a)
    (c : ℂ) (S : KGFamilyCarrier A →ₗ[ℂ] KGFamilyCarrier A) :
    kgFrameOperator g A (c • S)=c • kgFrameOperator g A S := by
  ext x
  exact (kgComparisonPoincare a g A.shape).map_smul c _

theorem kg_w9_original_response_continuation (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (q : ProperPoincareTransform) (r : PhysicalRay (fockCoreDomain a)) :
    kgW9OriginalResponse a s Ω (unitaryRayMap (kgCorePoincareIsometry a q) r)=
      kgOriginalRecordContinuation a s Ω q (kgW9OriginalResponse a s Ω r) := by
  rw [kg_w9_original_response_comparison,kg_w9_original_response_comparison]
  exact kg_original_quantum_record_continuation a s Ω q r

theorem kg_w9_complete_covariant_source (a : Parameters) (s : ℝ)
    (q : ProperPoincareTransform) (Ω : Opens CoordinatePoint)
    (r : PhysicalRay (fockCoreDomain a)) (π : WickMetricPathRoleProtocol Ω) :
    wickChartMetricPathRayOutput a s (wickAffineMetricRegion q.left.toAdd q.right Ω)
      (wickTransportedMetricDomain q.left.toAdd q.right Ω)
      (kgOriginalQuantumToRay a (unitaryRayMap (kgCorePoincareIsometry a q) r))
      (wickChartMetricPathProtocolPoincare a q (wickOriginalMetricPathInChart π))=
      wickIdentifiedMetricPathRecordReadout a s Ω (kgW9OriginalResponse a s Ω r) π := by
  rw [kg_w9_original_response_comparison]
  exact kg_original_quantum_complete_covariant_source a s q Ω r π

end AASCKleinGordon
