import KGCanonicalMetricLicensing
import KGNRReceivingCertificate
import KGScalarComparatorFourier
import KGNRFreeExactGenerator

/-! Canonical licensing of the actual NR core receiving-use family.
The full registered question family retains every original question and every
real NR time offset. Time evolution is the actual invariant-core flow, not an
EH history append. Comparison, tensor and regional consumer maps are constructed
separately between these fully quantified task instances. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace
open AASC.KernelReference AASCMetricityOriginalAssembly AASCMetricityLicensingConstruction
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) (A : KGNRObject a)

abbrev ScalarUseQuestion := RegisteredQuestion (KGNRReceivingQuestion a Ω A.shape)

def scalarOriginalProfile (x : PureVector (KGNRCarrier A)) : ScalarUseQuestion a Ω A → Option KGFamilyReadout :=
  (kgNRReceivingRegisteredOrbit a s Ω A.shape).references.referenceAt x

def scalarPureFlow (t : ℝ) (x : PureVector (KGNRCarrier A)) : PureVector (KGNRCarrier A) :=
  PureVector.mapUnitary (kgNRSpatialFamilyFlow a t A.shape) x

theorem scalar_original_profile_scalar (x y : PureVector (KGNRCarrier A))
    (same : PureVector.ScalarRel x y) : scalarOriginalProfile a s Ω A x = scalarOriginalProfile a s Ω A y := by
  funext q
  have record : ∀ q, kgNRReceivingOutput a s Ω A.shape x q = kgNRReceivingOutput a s Ω A.shape y q :=
    (kgNRReceivingRegisteredOrbit a s Ω A.shape).phase_output x y same
  cases q with
  | execution q =>
    change (if kgFamilySuccess (kgNRReceivingOutput a s Ω A.shape x q) then
      some (kgNRReceivingOutput a s Ω A.shape x q) else none) =
      (if kgFamilySuccess (kgNRReceivingOutput a s Ω A.shape y q) then
        some (kgNRReceivingOutput a s Ω A.shape y q) else none)
    rw [record q]
  | ledger q => exact congrArg some (record q)

structure OriginalScalarUseMeaning where
  parameters : Parameters
  originalPreparation : PureVector (KGNRCarrier A) → PureVector (KGFamilyCarrier A.raw)
  completeReference : PureVector (KGNRCarrier A) → ScalarUseQuestion a Ω A → Option KGFamilyReadout
  completeOutput : PureVector (KGNRCarrier A) → KGNRReceivingQuestion a Ω A.shape → KGFamilyReadout
  continuation : ℝ → PureVector (KGNRCarrier A) → PureVector (KGNRCarrier A)
  fullProjection : PhysicalRay (KGNRCarrier A) → PhysicalRay (kgNRFullFamilySpace A.shape)
  fullKineticDomain : Set KGNRSpatialHilbert
  fullKineticGraph : Set (KGNRSpatialHilbert × KGNRSpatialHilbert)
  fullScalarEvolution : ℝ → KGNRSpatialHilbert → KGNRSpatialHilbert
  referenceDispersion : KGSpatialSpace → ℝ

def originalScalarUseMeaning : OriginalScalarUseMeaning a Ω A :=
  ⟨a, kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a A.shape), scalarOriginalProfile a s Ω A,
    kgNRReceivingOutput a s Ω A.shape, scalarPureFlow a A, kgNRFullProjection a A.shape,
    (kgNRSpatialKinetic a).domain, (kgNRSpatialKinetic a).graph, fun t => kgNRSpatialFreeFlow a t,
    kgNRFrequencyKineticEnergy a⟩

def scalarSourceQualified (x : PureVector (KGNRCarrier A)) : Prop :=
  let original := kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a A.shape) x
  (kgRawRegisteredOrbit a s Ω A.raw).kernel.standing original
    (.execution (.comparison original)) (.comparison (transitionProbability original original))

theorem scalar_source_qualified (x : PureVector (KGNRCarrier A)) : scalarSourceQualified a s Ω A x :=
  kg_raw_registered_probability a s Ω A.raw _ _

def scalarContinuationWarrant (x : PureVector (KGNRCarrier A)) (t : ℝ)
    (y : PureVector (KGNRCarrier A)) : Prop :=
  y = scalarPureFlow a A t x ∧
    (∀ q, scalarOriginalProfile a s Ω A y q =
      scalarOriginalProfile a s Ω A x (mapRegisteredQuestion (kgNRQuestionAdvance t) q)) ∧
    (∀ word, kgFirstFailure (kgNRReceivingOutput a s Ω A.shape x) (word.map (kgNRQuestionAdvance t)) =
      kgFirstFailure (kgNRReceivingOutput a s Ω A.shape y) word) ∧
    kgNRFullProjection a A.shape (rayMap _ y) =
      unitaryRayMap (kgNRFullFamilyFlow a t A.shape) (kgNRFullProjection a A.shape (rayMap _ x))

def originalScalarAnswer (ground : ScalarUseQuestion a Ω A → Option KGFamilyReadout) :
    (q : Unit ⊕ ScalarUseQuestion a Ω A) →
      ProfileValue (fun _ => Option KGFamilyReadout) (OriginalScalarUseMeaning a Ω A) q → Prop
  | .inl _ => fun meaning => meaning = originalScalarUseMeaning a s Ω A
  | .inr q => fun value => value = ground q

def originalScalarTask :
    OriginalMetricTask (PureVector (KGNRCarrier A)) (PureVector (KGNRCarrier A))
      (ScalarUseQuestion a Ω A → Option KGFamilyReadout) (OriginalScalarUseMeaning a Ω A)
      Unit ℝ (ScalarUseQuestion a Ω A) (fun _ => Option KGFamilyReadout)
      (PureVector (KGNRCarrier A)) (OriginalScalarUseMeaning a Ω A)
      (OriginalScalarUseMeaning a Ω A) (ScalarUseQuestion a Ω A → Option KGFamilyReadout) where
  act := id
  ground := scalarOriginalProfile a s Ω A
  descriptor := fun _ => originalScalarUseMeaning a s Ω A
  descriptorMeaning := id
  answers := scalarOriginalProfile a s Ω A
  qualification := fun ground witness => scalarOriginalProfile a s Ω A witness = ground ∧ scalarSourceQualified a s Ω A witness
  originalAnswer := originalScalarAnswer a s Ω A
  originalLocal := fun x => (kgNRReceivingRegisteredOrbit a s Ω A.shape).kernel.standing x
    (.execution ((kgNRReceivingRegisteredOrbit a s Ω A.shape).outgoing x))
    (.comparison (transitionProbability x x))
  redescription := PureVector.ScalarRel
  redEdge := fun x _ y => PureVector.ScalarRel x y
  contEdge := fun x t y => y = scalarPureFlow a A t x
  redOriginalWarrant := fun x _ y => PureVector.ScalarRel x y
  contOriginalWarrant := scalarContinuationWarrant a s Ω A
  context := fun _ => originalScalarUseMeaning a s Ω A
  boundaryWork := id

theorem original_scalar_answers_determinate :
    DependentConservation.Determinate (originalScalarTask a s Ω A).originalAnswer := by
  intro ground q x y hx hy
  cases q with
  | inl _ => exact hx.trans hy.symm
  | inr _ => exact hx.trans hy.symm

theorem every_original_scalar_passes_local_tests (x : PureVector (KGNRCarrier A)) :
    originalLocalTest (originalScalarTask a s Ω A) x := by
  refine ⟨⟨x, rfl, scalar_source_qualified a s Ω A x⟩, ?_,
    (kgNRReceivingRegisteredOrbit a s Ω A.shape).raw_probability_standing x x, ?_⟩
  · intro q
    cases q <;> rfl
  · intro y same
    exact ⟨(), y, same, rfl⟩

theorem original_scalar_region_postfixed :
    (Set.univ : Set (PureVector (KGNRCarrier A))) ⊆
      originalSafetyOperator (originalScalarTask a s Ω A) Set.univ := by
  intro x _
  refine ⟨every_original_scalar_passes_local_tests a s Ω A x, ?_⟩
  intro t y edge
  cases t with
  | inl _ => exact ⟨⟨edge, (scalar_original_profile_scalar a s Ω A x y edge).symm⟩, Set.mem_univ _⟩
  | inr t =>
    change y = scalarPureFlow a A t x at edge
    subst y
    refine ⟨⟨rfl, ?_, ?_, ?_⟩, Set.mem_univ _⟩
    · intro q
      exact (kg_nr_receiving_continuation_reference a s t Ω A.shape x q).symm
    · exact kg_nr_receiving_continuation_first_failure a s t Ω A.shape x
    · exact kg_nr_full_projection_ray_continuation a t A.shape x

theorem every_original_scalar_has_canonical_license (x : PureVector (KGNRCarrier A)) :
    constructedLicensing (originalScalarTask a s Ω A) x (originalScalarUseMeaning a s Ω A) :=
  canonical_licensing_contains_every_original_sound_region _ Set.univ
    (original_scalar_region_postfixed a s Ω A) x (Set.mem_univ x)

theorem scalar_use_constructs_kernel_and_canonical_license :
    let D := originalScalarTask a s Ω A
    AASC.Instances.KernelPaper.Manuscript.DerivedKernelRoles
      (ObjecthoodNecessity.canonicalRegime (originalIncidence D)) ∧
    AASCAMetricMetricUse.AMetricLicensingDiscipline ∧ FiveLicensingConclusions D ∧
    (∀ x, constructedLicensing D x (originalScalarUseMeaning a s Ω A)) := by
  let x : PureVector (KGNRCarrier A) := kgNRFamilyPreparation a A.shape
  have assembly := kernel_ametric_canonical_metric_licensing (originalScalarTask a s Ω A)
    (original_scalar_answers_determinate a s Ω A)
    ⟨scalarOriginalProfile a s Ω A x, x, rfl, scalar_source_qualified a s Ω A x⟩
  exact ⟨assembly.1, assembly.2.2.1, assembly.2.2.2.2.2,
    every_original_scalar_has_canonical_license a s Ω A⟩

end AASCKleinGordon.CanonicalLicensing
