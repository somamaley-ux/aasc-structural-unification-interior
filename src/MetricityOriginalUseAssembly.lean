import AMetricMetricUseRestrictions
import MetricityCanonicalLicensingInterface

/-! Full Metricity equations (4)-(7) and Theorem 6.2, in normalized original
semantic result types. Raw presentations remain distinct; `ground` indexes the
original bearer/occurrence/complete question and conditions, not components in
a particular frame. Partial answers can use Option, or Boolean graph queries.
The task structure has data only. None of L1-L5, safety, licensing, minimality,
or a field asserting correct transport is an input. Unsafe edges remain in R.
Local/edge requirements below are original semantic tests, not license fields. -/
namespace AASCMetricityOriginalAssembly
noncomputable section
set_option autoImplicit false
open AASC.KernelReference
open AASCMetricityOrderAudit
open AASCMetricityLicensingConstruction

def ProfileValue {Q : Type} (V : Q → Type) (Meaning : Type) : Unit ⊕ Q → Type
  | .inl _ => Meaning
  | .inr q => V q

structure OriginalMetricTask (C A Origin M RedTag ContTag Q : Type)
    (V : Q → Type) (Witness Meaning Context Boundary : Type) where
  act : C → A
  ground : A → Origin
  descriptor : C → M
  descriptorMeaning : M → Meaning
  answers : (c : C) → (q : Q) → V q
  qualification : Origin → Witness → Prop
  originalAnswer : (origin : Origin) → (q : Unit ⊕ Q) → ProfileValue V Meaning q → Prop
  originalLocal : C → Prop
  redescription : A → A → Prop
  redEdge : C → RedTag → C → Prop
  contEdge : C → ContTag → C → Prop
  redOriginalWarrant : C → RedTag → C → Prop
  contOriginalWarrant : C → ContTag → C → Prop
  context : Origin → Context
  boundaryWork : Origin → Boundary

variable {C A Origin M RedTag ContTag Q : Type} {V : Q → Type}
  {Witness Meaning Context Boundary : Type}
local notation "Task" => OriginalMetricTask C A Origin M RedTag ContTag Q V Witness Meaning Context Boundary

def originalIncidence (D : Task) : IncidenceNecessity.Incidence Origin Unit (fun _ => Witness) :=
  fun origin _ witness => D.qualification origin witness

def completeOriginalProfile (D : Task) (c : C) : (q : Unit ⊕ Q) → ProfileValue V Meaning q
  | .inl _ => D.descriptorMeaning (D.descriptor c)
  | .inr q => D.answers c q

def OriginalReadiness (D : Task) (c : C) : Prop :=
  ∀ a', D.redescription (D.act c) a' → ∃ t d,D.redEdge c t d ∧ D.act d=a'

def originalLocalTest (D : Task) (c : C) : Prop :=
  IncidenceNecessity.Qualified (originalIncidence D) (D.ground (D.act c)) () ∧
  (∀ q,D.originalAnswer (D.ground (D.act c)) q (completeOriginalProfile D c q)) ∧
  D.originalLocal c ∧ OriginalReadiness D c

def declaredOriginalEdge (D : Task) (c : C) : RedTag ⊕ ContTag → C → Prop
  | .inl t => D.redEdge c t
  | .inr t => D.contEdge c t

def originalEdgeTest (D : Task) (c : C) : RedTag ⊕ ContTag → C → Prop
  | .inl t => fun d => D.redOriginalWarrant c t d ∧ D.ground (D.act d)=D.ground (D.act c)
  | .inr t => D.contOriginalWarrant c t

def canonicalSafeUses (D : Task) : Set C :=
  {c | OriginalSafe (originalLocalTest D) (declaredOriginalEdge D) (originalEdgeTest D) c}

def originalSafetyOperator (D : Task) (U : Set C) : Set C :=
  {c | originalLocalTest D c ∧ ∀ t d,declaredOriginalEdge D c t d →
    originalEdgeTest D c t d ∧ d ∈ U}

def constructedLicensing (D : Task) : A → M → Prop :=
  canonicalMetricLicense D.act D.descriptor (originalLocalTest D)
    (declaredOriginalEdge D) (originalEdgeTest D)

def originalDescriptorEquivalent (D : Task) (m m' : M) : Prop :=
  D.descriptorMeaning m=D.descriptorMeaning m'

theorem original_safety_operator_monotone (D : Task) : Monotone (originalSafetyOperator D) := by
  intro U V includes c hc
  exact ⟨hc.1,fun t d edge => ⟨(hc.2 t d edge).1,includes (hc.2 t d edge).2⟩⟩

theorem original_safety_postfixed_iff_sound (D : Task) (U : Set C) :
    U ⊆ originalSafetyOperator D U ↔
      OriginalSoundRegion (originalLocalTest D) (declaredOriginalEdge D) (originalEdgeTest D) U := Iff.rfl

theorem original_safe_uses_are_fixed (D : Task) :
    canonicalSafeUses D=originalSafetyOperator D (canonicalSafeUses D) := by
  apply Set.Subset.antisymm
  · exact original_safe_region_is_sound _ _ _
  · intro c hc
    have sound : OriginalSoundRegion (originalLocalTest D) (declaredOriginalEdge D)
        (originalEdgeTest D) (insert c (canonicalSafeUses D)) := by
      intro d hd
      rcases hd with rfl | hd
      · exact ⟨hc.1,fun t e edge => ⟨(hc.2 t e edge).1,Or.inr (hc.2 t e edge).2⟩⟩
      · have hs := original_safe_region_is_sound (originalLocalTest D)
          (declaredOriginalEdge D) (originalEdgeTest D) d hd
        exact ⟨hs.1,fun t e edge => ⟨(hs.2 t e edge).1,Or.inr (hs.2 t e edge).2⟩⟩
    exact original_sound_region_is_safe _ _ _ _ sound c (Or.inl rfl)

theorem original_safe_uses_are_union_of_all_sound_regions (D : Task) :
    canonicalSafeUses D=⋃₀ {U : Set C | U ⊆ originalSafetyOperator D U} := by
  apply Set.Subset.antisymm
  · intro c hc
    exact ⟨canonicalSafeUses D,(original_safe_uses_are_fixed D).le,hc⟩
  · rintro c ⟨U,sound,hc⟩
    exact original_sound_region_is_safe _ _ _ U sound c hc

theorem licensing_exact_original_safe_projection (D : Task) (a : A) (m : M) :
    constructedLicensing D a m ↔ ∃ c,c ∈ canonicalSafeUses D ∧ D.act c=a ∧ D.descriptor c=m := Iff.rfl

theorem licensed_original_incidence_witness (D : Task) (a : A) (m : M)
    (licensed : constructedLicensing D a m) : ∃ witness,D.qualification (D.ground a) witness := by
  obtain ⟨c,safe,rfl,_⟩ := licensed
  exact (safe c Relation.ReflTransGen.refl).1.1

theorem L1_licensed_act_has_original_standing (D : Task) (a : A) (m : M)
    (licensed : constructedLicensing D a m) :
    IncidenceNecessity.assess (originalIncidence D) (D.ground a) ()=true :=
  (IncidenceNecessity.assess_true_iff _ _ _).mpr (licensed_original_incidence_witness D a m licensed)

theorem safe_redescription_has_same_original_ground (D : Task) (c d : C) (t : RedTag)
    (safe : c ∈ canonicalSafeUses D) (edge : D.redEdge c t d) :
    D.ground (D.act d)=D.ground (D.act c) ∧ d ∈ canonicalSafeUses D := by
  have hs := original_safe_successor (originalLocalTest D) (declaredOriginalEdge D)
    (originalEdgeTest D) c d (.inl t) safe edge
  exact ⟨hs.1.2,hs.2⟩

theorem safe_redescription_has_equal_complete_profile (D : Task)
    (determinate : DependentConservation.Determinate D.originalAnswer)
    (c d : C) (t : RedTag) (safe : c ∈ canonicalSafeUses D) (edge : D.redEdge c t d) :
    completeOriginalProfile D d=completeOriginalProfile D c := by
  obtain ⟨same,dsafe⟩ := safe_redescription_has_same_original_ground D c d t safe edge
  exact DependentConservation.profile_eq_of_same_bearer D.originalAnswer determinate same
    (completeOriginalProfile D d) (completeOriginalProfile D c)
    (dsafe d Relation.ReflTransGen.refl).1.2.1 (safe c Relation.ReflTransGen.refl).1.2.1

theorem L2_every_required_redescription_is_licensed (D : Task)
    (determinate : DependentConservation.Determinate D.originalAnswer)
    (a a' : A) (m : M) (licensed : constructedLicensing D a m) (red : D.redescription a a') :
    ∃ m',originalDescriptorEquivalent D m' m ∧ constructedLicensing D a' m' := by
  obtain ⟨c,safe,rfl,rfl⟩ := licensed
  obtain ⟨t,d,edge,actEq⟩ := (safe c Relation.ReflTransGen.refl).1.2.2.2 a' red
  have dsafe := (safe_redescription_has_same_original_ground D c d t safe edge).2
  have profile := safe_redescription_has_equal_complete_profile D determinate c d t safe edge
  exact ⟨D.descriptor d,congrFun profile (.inl ()),d,dsafe,actEq,rfl⟩

theorem L3_original_boundary_work_and_context_are_preserved (D : Task)
    (determinate : DependentConservation.Determinate D.originalAnswer)
    (c d : C) (t : RedTag) (safe : c ∈ canonicalSafeUses D) (edge : D.redEdge c t d) :
    D.context (D.ground (D.act d))=D.context (D.ground (D.act c)) ∧
    D.boundaryWork (D.ground (D.act d))=D.boundaryWork (D.ground (D.act c)) ∧
    completeOriginalProfile D d=completeOriginalProfile D c := by
  have same := (safe_redescription_has_same_original_ground D c d t safe edge).1
  exact ⟨congrArg D.context same,congrArg D.boundaryWork same,
    safe_redescription_has_equal_complete_profile D determinate c d t safe edge⟩

theorem L4_every_declared_finite_path_retains_original_warrants (D : Task)
    (c : C) (safe : c ∈ canonicalSafeUses D) :
    ∀ d,Relation.ReflTransGen (DeclaredStep (declaredOriginalEdge D)) c d →
      d ∈ canonicalSafeUses D ∧ constructedLicensing D (D.act d) (D.descriptor d) ∧
      ∀ t e,declaredOriginalEdge D d t e → originalEdgeTest D d t e := by
  intro d path
  have dsafe : d ∈ canonicalSafeUses D := by
    intro e tail
    exact safe e (path.trans tail)
  exact ⟨dsafe,⟨d,dsafe,rfl,rfl⟩,(safe d path).2⟩

/-- The non-generation assertion is original-ground dependence and non-override,
not a formal claim that no physical constructor can create a new object. -/
theorem L5_licensing_cannot_supply_a_missing_original_incidence (D : Task) (a : A)
    (missing : ¬ ∃ witness,D.qualification (D.ground a) witness) :
    ∀ m,¬ constructedLicensing D a m := by
  intro m licensed
  exact missing (licensed_original_incidence_witness D a m licensed)

theorem L5_retaining_original_subject_precludes_retroactive_repair (D : Task)
    (a a' : A) (same : D.ground a=D.ground a')
    (failed : IncidenceNecessity.assess (originalIncidence D) (D.ground a) ()=false) :
    ∀ m,¬ constructedLicensing D a' m := by
  intro m licensed
  have positive := L1_licensed_act_has_original_standing D a' m licensed
  rw [← same,failed] at positive
  cases positive

def FiveLicensingConclusions (D : Task) : Prop :=
  (∀ a m,constructedLicensing D a m →
    IncidenceNecessity.assess (originalIncidence D) (D.ground a) ()=true) ∧
  (∀ a a' m,constructedLicensing D a m → D.redescription a a' →
    ∃ m',originalDescriptorEquivalent D m' m ∧ constructedLicensing D a' m') ∧
  (∀ c d t,c ∈ canonicalSafeUses D → D.redEdge c t d →
    D.context (D.ground (D.act d))=D.context (D.ground (D.act c)) ∧
    D.boundaryWork (D.ground (D.act d))=D.boundaryWork (D.ground (D.act c)) ∧
    completeOriginalProfile D d=completeOriginalProfile D c) ∧
  (∀ c,c ∈ canonicalSafeUses D →
    ∀ d,Relation.ReflTransGen (DeclaredStep (declaredOriginalEdge D)) c d →
      d ∈ canonicalSafeUses D ∧ constructedLicensing D (D.act d) (D.descriptor d) ∧
      ∀ t e,declaredOriginalEdge D d t e → originalEdgeTest D d t e) ∧
  (∀ a,(¬ ∃ witness,D.qualification (D.ground a) witness) →
    ∀ m,¬ constructedLicensing D a m)

theorem canonical_original_use_construction_proves_L1_through_L5 (D : Task)
    (determinate : DependentConservation.Determinate D.originalAnswer) : FiveLicensingConclusions D := by
  exact ⟨L1_licensed_act_has_original_standing D,
    L2_every_required_redescription_is_licensed D determinate,
    L3_original_boundary_work_and_context_are_preserved D determinate,
    L4_every_declared_finite_path_retains_original_warrants D,
    L5_licensing_cannot_supply_a_missing_original_incidence D⟩

theorem canonical_licensing_contains_every_original_sound_region (D : Task) (U : Set C)
    (sound : U ⊆ originalSafetyOperator D U) :
    ∀ c ∈ U,constructedLicensing D (D.act c) (D.descriptor c) :=
  every_original_sound_region_is_in_canonical_license D.act D.descriptor
    (originalLocalTest D) (declaredOriginalEdge D) (originalEdgeTest D) U sound

/-- Full assembly: raw actual incidence supplies the actual public Kernel;
AMetric information/grounding restrictions are proved, not fields; equations
4-7 and all five licensing properties are conclusions. No interface order is
an input because existence of a local minimum is a separate reserved claim. -/
theorem kernel_ametric_canonical_metric_licensing (D : Task)
    (determinate : DependentConservation.Determinate D.originalAnswer)
    (actual : ∃ origin witness,D.qualification origin witness) :
    AASC.Instances.KernelPaper.Manuscript.DerivedKernelRoles
      (ObjecthoodNecessity.canonicalRegime (originalIncidence D)) ∧
    (∀ origin, (ObjecthoodNecessity.canonicalRegime (originalIncidence D)).Standing (origin,()) ↔
      IncidenceNecessity.Qualified (originalIncidence D) origin ()) ∧
    AASCAMetricMetricUse.AMetricLicensingDiscipline ∧
    canonicalSafeUses D=originalSafetyOperator D (canonicalSafeUses D) ∧
    canonicalSafeUses D=⋃₀ {U : Set C | U ⊆ originalSafetyOperator D U} ∧
    FiveLicensingConclusions D := by
  have kernel := ObjecthoodNecessity.original_incidence_constructs_kernel (originalIncidence D)
    (by obtain ⟨origin,witness,h⟩ := actual; exact ⟨origin,(),witness,h⟩)
  exact ⟨kernel.1,fun origin => kernel.2.1 origin (),
    AASCAMetricMetricUse.constructed_ametric_licensing_discipline,
    original_safe_uses_are_fixed D,original_safe_uses_are_union_of_all_sound_regions D,
    canonical_original_use_construction_proves_L1_through_L5 D determinate⟩

#print axioms ProfileValue
#print axioms OriginalMetricTask
#print axioms originalIncidence
#print axioms completeOriginalProfile
#print axioms OriginalReadiness
#print axioms originalLocalTest
#print axioms declaredOriginalEdge
#print axioms originalEdgeTest
#print axioms canonicalSafeUses
#print axioms originalSafetyOperator
#print axioms constructedLicensing
#print axioms originalDescriptorEquivalent
#print axioms original_safety_operator_monotone
#print axioms original_safety_postfixed_iff_sound
#print axioms original_safe_uses_are_fixed
#print axioms original_safe_uses_are_union_of_all_sound_regions
#print axioms licensing_exact_original_safe_projection
#print axioms licensed_original_incidence_witness
#print axioms L1_licensed_act_has_original_standing
#print axioms safe_redescription_has_same_original_ground
#print axioms safe_redescription_has_equal_complete_profile
#print axioms L2_every_required_redescription_is_licensed
#print axioms L3_original_boundary_work_and_context_are_preserved
#print axioms L4_every_declared_finite_path_retains_original_warrants
#print axioms L5_licensing_cannot_supply_a_missing_original_incidence
#print axioms L5_retaining_original_subject_precludes_retroactive_repair
#print axioms FiveLicensingConclusions
#print axioms canonical_original_use_construction_proves_L1_through_L5
#print axioms canonical_licensing_contains_every_original_sound_region
#print axioms kernel_ametric_canonical_metric_licensing
end
end AASCMetricityOriginalAssembly
