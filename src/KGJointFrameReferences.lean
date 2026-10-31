import KGJointFrameProjections

/-! Metric questions transform as linear functionals under the actual field
congruence. Component entries are not treated as invariant scalars. The other
questions are the actual original registered chart protocols. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace AASCSemanticExhaustion
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

abbrev KGJointFrameQuestion {a : Parameters} (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) :=
  (Spacetime × (NativeRealMatrix →ₗ[ℝ] ℝ)) ⊕
    RegisteredQuestion (KGChartFamilyQuestion a Ω (wickOriginalMetricNeighborhood Ω) A)

def kgJointFrameMatrixEntry (i j : Fin 4) : NativeRealMatrix →ₗ[ℝ] ℝ where
  toFun G := G i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def kgJointFrameFieldAnswer (q : ProperPoincareTransform) (g : Spacetime → NativeRealMatrix)
    (p : Spacetime) (ℓ : NativeRealMatrix →ₗ[ℝ] ℝ) : ℝ :=
  ℓ ((wickLorentzMatrix q.right).transpose*
    g (q.left.toAdd+spacetimeLorentzCLE q.right p)*wickLorentzMatrix q.right)

def kgJointFrameOriginalAnswer {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (x : KGJointFrameOriginal s Ω A) :
    KGJointFrameQuestion Ω A → Option KGPreparedReadout
  | .inl (p,ℓ) => some (.inl (ℓ (kgPreparedMetricField s Ω (wickOriginalMetricNeighborhood Ω) A x p)))
  | .inr π => (kgPreparedReferences s Ω (wickOriginalMetricNeighborhood Ω) A).referenceAt x (.inr π)

def kgJointFrameAnswer {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (q : ProperPoincareTransform) (x : KGJointFrameUse s Ω A q) :
    KGJointFrameQuestion Ω A → Option KGPreparedReadout
  | .inl (p,ℓ) => some (.inl (kgJointFrameFieldAnswer q
      (kgPreparedMetricField s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω) A x) p ℓ))
  | .inr π =>
      (kgPreparedReferences s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω) A).referenceAt
        x (.inr (mapRegisteredQuestion (kgChartFamilyQuestionFrame a q) π))

theorem kg_joint_frame_answer_original {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (q : ProperPoincareTransform) (x : KGJointFrameOriginal s Ω A)
    (π : KGJointFrameQuestion Ω A) :
    kgJointFrameAnswer s Ω A q (kgJointFramePreparedEquiv s Ω A q x) π=
      kgJointFrameOriginalAnswer s Ω A x π := by
  cases π with
  | inl test =>
    obtain ⟨p,ℓ⟩ := test
    change (some (Sum.inl (kgJointFrameFieldAnswer q
      (kgPreparedMetricField s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω) A
        (kgJointFramePreparedEquiv s Ω A q x)) p ℓ)) : Option KGPreparedReadout)=
      some (Sum.inl (ℓ (kgPreparedMetricField s Ω (wickOriginalMetricNeighborhood Ω) A x p)))
    unfold kgJointFrameFieldAnswer
    rw [kg_joint_frame_metric_field,kg_metric_act_inverse_congruence]
  | inr π => exact kg_joint_frame_registered_reference s Ω A q x π

theorem kg_joint_frame_change_answer {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (p q : ProperPoincareTransform) (x : KGJointFrameUse s Ω A p)
    (π : KGJointFrameQuestion Ω A) :
    kgJointFrameAnswer s Ω A q (kgJointFrameChange s Ω A p q x) π=
      kgJointFrameAnswer s Ω A p x π := by
  have left := kg_joint_frame_answer_original s Ω A q
    ((kgJointFramePreparedEquiv s Ω A p).symm x) π
  have right := kg_joint_frame_answer_original s Ω A p
    ((kgJointFramePreparedEquiv s Ω A p).symm x) π
  rw [Equiv.apply_symm_apply] at right
  exact left.trans right.symm

theorem kg_joint_frame_prepared_field_reference {a : Parameters} (s : ℝ)
    (Ω : Opens CoordinatePoint) (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a)
    (x : KGPreparedMetricUse s Ω D A) (p : Spacetime) (i j : Fin 4) :
    (kgPreparedReferences s Ω D A).referenceAt x (.inl (p,i,j))=
      some (.inl (kgPreparedMetricField s Ω D A x p i j)) := by
  induction x using Quotient.inductionOn with | _ x => rfl

theorem kg_joint_frame_original_profile_faithful {a : Parameters} (s : ℝ)
    (Ω : Opens CoordinatePoint) (A : KGFamilyObject a) (x y : KGJointFrameOriginal s Ω A)
    (same : ∀ π,kgJointFrameOriginalAnswer s Ω A x π=kgJointFrameOriginalAnswer s Ω A y π) : x=y := by
  apply kg_prepared_reference_profile_faithful s Ω (wickOriginalMetricNeighborhood Ω) A
  intro π
  cases π with
  | inl point =>
    obtain ⟨p,i,j⟩ := point
    rw [kg_joint_frame_prepared_field_reference,kg_joint_frame_prepared_field_reference]
    exact same (.inl (p,kgJointFrameMatrixEntry i j))
  | inr π => exact same (.inr π)

theorem kg_joint_frame_profile_faithful {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (q : ProperPoincareTransform) (x y : KGJointFrameUse s Ω A q)
    (same : ∀ π,kgJointFrameAnswer s Ω A q x π=kgJointFrameAnswer s Ω A q y π) : x=y := by
  apply (kgJointFramePreparedEquiv s Ω A q).symm.injective
  apply kg_joint_frame_original_profile_faithful s Ω A
  intro π
  have left := kg_joint_frame_answer_original s Ω A q ((kgJointFramePreparedEquiv s Ω A q).symm x) π
  have right := kg_joint_frame_answer_original s Ω A q ((kgJointFramePreparedEquiv s Ω A q).symm y) π
  rw [Equiv.apply_symm_apply] at left right
  exact left.symm.trans ((same π).trans right)

abbrev KGJointFrameLocus {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) := Σ q : ProperPoincareTransform,KGJointFrameUse s Ω A q

def kgJointFrameFamilyReferences {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) :
    AASC.PartialReferenceSystem (KGJointFrameLocus s Ω A) (KGJointFrameQuestion Ω A) KGPreparedReadout :=
  ⟨fun x => kgJointFrameAnswer s Ω A x.1 x.2⟩

def kgJointFrameLocusChange {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (q : ProperPoincareTransform) (x : KGJointFrameLocus s Ω A) :
    KGJointFrameLocus s Ω A := ⟨q,kgJointFrameChange s Ω A x.1 q x.2⟩

theorem kg_joint_frame_locus_identity {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (x : KGJointFrameLocus s Ω A) :
    kgJointFrameLocusChange s Ω A x.1 x=x := by
  obtain ⟨p,x⟩ := x
  change Sigma.mk p (kgJointFrameChange s Ω A p p x)=Sigma.mk p x
  rw [kg_joint_frame_change_identity]

theorem kg_joint_frame_locus_composition {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (p q : ProperPoincareTransform) (x : KGJointFrameLocus s Ω A) :
    kgJointFrameLocusChange s Ω A q (kgJointFrameLocusChange s Ω A p x)=
      kgJointFrameLocusChange s Ω A q x := by
  obtain ⟨r,x⟩ := x
  change Sigma.mk q (kgJointFrameChange s Ω A p q (kgJointFrameChange s Ω A r p x))=
    Sigma.mk q (kgJointFrameChange s Ω A r q x)
  rw [kg_joint_frame_change_composition]

theorem kg_joint_frame_family_reference_square {a : Parameters} (s : ℝ)
    (Ω : Opens CoordinatePoint) (A : KGFamilyObject a) (q : ProperPoincareTransform)
    (x : KGJointFrameLocus s Ω A) (π : KGJointFrameQuestion Ω A) :
    (kgJointFrameFamilyReferences s Ω A).referenceAt (kgJointFrameLocusChange s Ω A q x) π=
      (kgJointFrameFamilyReferences s Ω A).referenceAt x π :=
  kg_joint_frame_change_answer s Ω A x.1 q x.2 π

def kgJointFrameIncidenceContinuation {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (q : ProperPoincareTransform)
    (x : KGJointFrameLocus s Ω A) (π : KGJointFrameQuestion Ω A) :
    (kgJointFrameFamilyReferences s Ω A).incidenceSystem.Continuation
      (x,π) (kgJointFrameLocusChange s Ω A q x,π) where
  map reference := ⟨reference.value,by
    change (kgJointFrameFamilyReferences s Ω A).referenceAt _ π=some reference.value
    rw [kg_joint_frame_family_reference_square]
    exact reference.isIncident⟩

theorem kg_joint_frame_family_standing {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (q : ProperPoincareTransform)
    (x : KGJointFrameLocus s Ω A) (π : KGJointFrameQuestion Ω A) :
    (kgJointFrameFamilyReferences s Ω A).incidenceSystem.AdmissibleAt
      (kgJointFrameLocusChange s Ω A q x) π ↔
      (kgJointFrameFamilyReferences s Ω A).incidenceSystem.AdmissibleAt x π := by
  change (∃ v,(kgJointFrameFamilyReferences s Ω A).referenceAt
    (kgJointFrameLocusChange s Ω A q x) π=some v) ↔
    (∃ v,(kgJointFrameFamilyReferences s Ω A).referenceAt x π=some v)
  rw [kg_joint_frame_family_reference_square]

theorem kg_joint_frame_family_failure {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (q : ProperPoincareTransform)
    (x : KGJointFrameLocus s Ω A) (π : KGJointFrameQuestion Ω A) :
    (kgJointFrameFamilyReferences s Ω A).kernel.FailureAt
      (kgJointFrameLocusChange s Ω A q x) π ↔
      (kgJointFrameFamilyReferences s Ω A).kernel.FailureAt x π := by
  change (∀ v,¬ (kgJointFrameFamilyReferences s Ω A).referenceAt
    (kgJointFrameLocusChange s Ω A q x) π=some v) ↔
    (∀ v,¬ (kgJointFrameFamilyReferences s Ω A).referenceAt x π=some v)
  rw [kg_joint_frame_family_reference_square]

theorem kg_joint_frame_family_no_repair {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (q : ProperPoincareTransform)
    (x : KGJointFrameLocus s Ω A) (π : KGJointFrameQuestion Ω A)
    (failed : (kgJointFrameFamilyReferences s Ω A).kernel.FailureAt x π) :
    ¬ (kgJointFrameFamilyReferences s Ω A).incidenceSystem.AdmissibleAt
      (kgJointFrameLocusChange s Ω A q x) π := by
  have none := ((kgJointFrameFamilyReferences s Ω A).referenceAt_eq_none_iff x π).mpr failed
  rintro ⟨v,hv⟩
  change (kgJointFrameFamilyReferences s Ω A).referenceAt _ π=some v at hv
  rw [kg_joint_frame_family_reference_square,none] at hv
  cases hv

end AASCKleinGordon
