import MetricityOriginalOrderScope
import KernelReference.ContextualQuotient

/-! Metricity 6.1-6.5: construct the complete safe-use licensing receiver.
The task data, query family, descriptor family and original physical order are
inputs, fixed independently of this receiver. Physical identification is not
inferred from the receiver's information universal property. -/
namespace AASCMetricityLicensingConstruction
noncomputable section
set_option autoImplicit false
open AASCMetricityOrderAudit
open AASC.KernelReference
variable {C T A M : Type}

def originalMetricLocal (qualification : A → Prop) (act : C → A)
    (otherLocal : C → Prop) (c : C) : Prop :=
  qualification (act c) ∧ otherLocal c

theorem original_safe_has_qualification (qualification : A → Prop) (act : C → A)
    (otherLocal : C → Prop) (R W : C → T → C → Prop) (c : C)
    (safe : OriginalSafe (originalMetricLocal qualification act otherLocal) R W c) :
    qualification (act c) :=
  (safe c Relation.ReflTransGen.refl).1.1

theorem original_safe_successor (AD : C → Prop) (R W : C → T → C → Prop)
    (c d : C) (t : T) (safe : OriginalSafe AD R W c) (edge : R c t d) :
    W c t d ∧ OriginalSafe AD R W d := by
  refine ⟨(safe c Relation.ReflTransGen.refl).2 t d edge, ?_⟩
  intro e path
  exact safe e ((Relation.ReflTransGen.single ⟨t,edge⟩).trans path)

def OriginalSoundRegion (AD : C → Prop) (R W : C → T → C → Prop) (U : Set C) : Prop :=
  ∀ c ∈ U, AD c ∧ ∀ t d, R c t d → W c t d ∧ d ∈ U

theorem original_sound_region_is_safe (AD : C → Prop) (R W : C → T → C → Prop)
    (U : Set C) (sound : OriginalSoundRegion AD R W U) :
    ∀ c ∈ U, OriginalSafe AD R W c := by
  intro c hc d path
  have hd : d ∈ U := by
    induction path with
    | refl => exact hc
    | @tail b e path step ih =>
      obtain ⟨t,edge⟩ := step
      exact (sound b ih).2 t e edge |>.2
  exact ⟨(sound d hd).1,fun t e edge => ((sound d hd).2 t e edge).1⟩

theorem original_safe_region_is_sound (AD : C → Prop) (R W : C → T → C → Prop) :
    OriginalSoundRegion AD R W {c | OriginalSafe AD R W c} := by
  intro c hc
  exact ⟨(hc c Relation.ReflTransGen.refl).1,
    fun t d edge => original_safe_successor AD R W c d t hc edge⟩

def canonicalMetricLicense (act : C → A) (descriptor : C → M)
    (AD : C → Prop) (R W : C → T → C → Prop) (a : A) (m : M) : Prop :=
  ∃ c, OriginalSafe AD R W c ∧ act c = a ∧ descriptor c = m

theorem canonical_license_has_original_qualification (qualification : A → Prop)
    (act : C → A) (descriptor : C → M) (otherLocal : C → Prop)
    (R W : C → T → C → Prop) (a : A) (m : M)
    (licensed : canonicalMetricLicense act descriptor
      (originalMetricLocal qualification act otherLocal) R W a m) : qualification a := by
  obtain ⟨c,safe,rfl,_⟩ := licensed
  exact original_safe_has_qualification qualification act otherLocal R W c safe

theorem every_original_sound_region_is_in_canonical_license
    (act : C → A) (descriptor : C → M) (AD : C → Prop)
    (R W : C → T → C → Prop) (U : Set C)
    (sound : OriginalSoundRegion AD R W U) :
    ∀ c ∈ U, canonicalMetricLicense act descriptor AD R W (act c) (descriptor c) := by
  intro c hc
  exact ⟨c,original_sound_region_is_safe AD R W U sound c hc,rfl,rfl⟩

theorem safe_use_preserves_original_edge_and_successor_license
    (act : C → A) (descriptor : C → M) (AD : C → Prop)
    (R W : C → T → C → Prop) (c d : C) (t : T)
    (safe : OriginalSafe AD R W c) (edge : R c t d) :
    W c t d ∧ canonicalMetricLicense act descriptor AD R W (act d) (descriptor d) := by
  obtain ⟨warrant,successor⟩ := original_safe_successor AD R W c d t safe edge
  exact ⟨warrant,d,successor,rfl,rfl⟩

abbrev SafeOriginalMetricRecords (AD : C → Prop) (R W : C → T → C → Prop) :=
  {c : C // OriginalSafe AD R W c}

variable {Q : Type} {V : Q → Type}

/-- The single bundle contains every original dependent answer, not one bit.
Act and descriptor are retained separately even if already present in the profile. -/
def completeLicensedObservation (act : C → A) (descriptor : C → M)
    (observe : (c : C) → (q : Q) → V q)
    (AD : C → Prop) (R W : C → T → C → Prop)
    (c : SafeOriginalMetricRecords AD R W) (_ : Unit) :
    (A × M) × ((q : Q) → V q) := ((act c.val,descriptor c.val),observe c.val)

abbrev CanonicalLicensingReceiver (act : C → A) (descriptor : C → M)
    (observe : (c : C) → (q : Q) → V q)
    (AD : C → Prop) (R W : C → T → C → Prop) :=
  ContextualQuotient.ObservedProfiles
    (completeLicensedObservation act descriptor observe AD R W)

def presentSafeOriginalUse (act : C → A) (descriptor : C → M)
    (observe : (c : C) → (q : Q) → V q)
    (AD : C → Prop) (R W : C → T → C → Prop)
    (c : SafeOriginalMetricRecords AD R W) :
    CanonicalLicensingReceiver act descriptor observe AD R W :=
  ContextualQuotient.profileImageMap
    (completeLicensedObservation act descriptor observe AD R W) c

theorem constructed_receipt_preserves_every_original_answer
    (act : C → A) (descriptor : C → M) (observe : (c : C) → (q : Q) → V q)
    (AD : C → Prop) (R W : C → T → C → Prop)
    (c : SafeOriginalMetricRecords AD R W) (q : Q) :
    ((presentSafeOriginalUse act descriptor observe AD R W c).val ()).2 q = observe c.val q := rfl

theorem constructed_receiver_exactly_presents_canonical_license
    (act : C → A) (descriptor : C → M) (observe : (c : C) → (q : Q) → V q)
    (AD : C → Prop) (R W : C → T → C → Prop) (a : A) (m : M) :
    canonicalMetricLicense act descriptor AD R W a m ↔
      ∃ r : CanonicalLicensingReceiver act descriptor observe AD R W,
        (r.val ()).1 = (a,m) := by
  constructor
  · rintro ⟨c,safe,ha,hm⟩
    refine ⟨presentSafeOriginalUse act descriptor observe AD R W ⟨c,safe⟩,?_⟩
    change (act c,descriptor c) = (a,m)
    exact Prod.ext ha hm
  · rintro ⟨r,hr⟩
    obtain ⟨c,hc⟩ := r.property
    have h : (act c.val,descriptor c.val) = (a,m) := by
      exact (congrArg (fun f => (f ()).1) hc).trans hr
    exact ⟨c.val,c.property,congrArg Prod.fst h,congrArg Prod.snd h⟩

theorem constructed_receiver_is_unique_exact_complete_content_receiver
    (act : C → A) (descriptor : C → M) (observe : (c : C) → (q : Q) → V q)
    (AD : C → Prop) (R W : C → T → C → Prop) :
    ∃! e : ContextualQuotient.CanonicalQuotient
        (completeLicensedObservation act descriptor observe AD R W) ≃
        CanonicalLicensingReceiver act descriptor observe AD R W,
      ∀ c, e (ContextualQuotient.classify
        (completeLicensedObservation act descriptor observe AD R W) c) =
        presentSafeOriginalUse act descriptor observe AD R W c :=
  ContextualQuotient.canonical_profile_realization _

/-- Sound-region transfer retains every target edge via an actual source lift.
This yields licensing at the received original use, not physical firstness. -/
theorem faithful_original_consumer_supplies_license {Y S : Type}
    (sourceLocal : Y → Prop) (sourceR sourceW : Y → S → Y → Prop)
    (U : Set Y) (sourceSound : OriginalSoundRegion sourceLocal sourceR sourceW U)
    (h : Y → C) (act : C → A) (descriptor : C → M)
    (AD : C → Prop) (R W : C → T → C → Prop)
    (localTransfer : ∀ y ∈ U, sourceLocal y → AD (h y))
    (lift : ∀ y ∈ U, ∀ t d, R (h y) t d →
      ∃ s y', sourceR y s y' ∧ h y' = d ∧ (sourceW y s y' → W (h y) t d)) :
    ∀ y ∈ U, canonicalMetricLicense act descriptor AD R W (act (h y)) (descriptor (h y)) := by
  have region : OriginalSoundRegion AD R W (h '' U) := by
    rintro c ⟨y,hy,rfl⟩
    refine ⟨localTransfer y hy (sourceSound y hy).1,?_⟩
    intro t d edge
    obtain ⟨s,y',se,he,hw⟩ := lift y hy t d edge
    exact ⟨hw ((sourceSound y hy).2 s y' se).1,
      ⟨y',((sourceSound y hy).2 s y' se).2,he⟩⟩
  intro y hy
  exact ⟨h y,original_sound_region_is_safe AD R W (h '' U) region (h y) ⟨y,hy,rfl⟩,rfl,rfl⟩

/-- Explicit residual physical prerequisite premise; not asserted for a native
candidate and not a consequence of quotient exactness. The existing order is
retained. Only the local predecessor cone is used, allowing incomparable minima. -/
theorem original_prerequisite_placement_and_positive_use_imply_local_boundary
    {I : Type} [Preorder I] (Bplace p : I)
    (useAt : I → M → C → Prop) (AD : C → Prop) (R W : C → T → C → Prop)
    (downstream : Bplace ≤ p)
    (m : M) (c : C) (placedUse : useAt p m c) (safe : OriginalSafe AD R W c)
    (prerequisitePlacement : ∀ q, q ≤ p → ∀ n d,
      useAt q n d → OriginalSafe AD R W d → p ≤ q) :
    LocalMetricBoundary Bplace p useAt AD R W := by
  refine ⟨downstream,⟨m,c,placedUse,safe⟩,?_⟩
  intro q earlier available
  obtain ⟨n,d,interpreted,qualified⟩ := available
  exact (not_le_of_gt earlier) (prerequisitePlacement q (le_of_lt earlier) n d interpreted qualified)

#print axioms originalMetricLocal
#print axioms original_safe_has_qualification
#print axioms original_safe_successor
#print axioms OriginalSoundRegion
#print axioms original_sound_region_is_safe
#print axioms original_safe_region_is_sound
#print axioms canonicalMetricLicense
#print axioms canonical_license_has_original_qualification
#print axioms every_original_sound_region_is_in_canonical_license
#print axioms safe_use_preserves_original_edge_and_successor_license
#print axioms SafeOriginalMetricRecords
#print axioms completeLicensedObservation
#print axioms CanonicalLicensingReceiver
#print axioms presentSafeOriginalUse
#print axioms constructed_receipt_preserves_every_original_answer
#print axioms constructed_receiver_exactly_presents_canonical_license
#print axioms constructed_receiver_is_unique_exact_complete_content_receiver
#print axioms faithful_original_consumer_supplies_license
#print axioms original_prerequisite_placement_and_positive_use_imply_local_boundary
end
end AASCMetricityLicensingConstruction
