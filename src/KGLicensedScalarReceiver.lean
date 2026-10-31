import KGCanonicalScalarLicensing
import KGNRFreeReceivingAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace CategoryTheory
open AASC.KernelReference AASCMetricityOriginalAssembly AASCMetricityLicensingConstruction
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
open scoped SchwartzMap

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) (A : KGNRObject a)

abbrev LicensedScalarReceiver :=
  let D := originalScalarTask a s Ω A
  CanonicalLicensingReceiver D.act D.descriptor D.answers
    (originalLocalTest D) (declaredOriginalEdge D) (originalEdgeTest D)

theorem original_scalar_is_safe (x : PureVector (KGNRCarrier A)) :
    x ∈ canonicalSafeUses (originalScalarTask a s Ω A) :=
  original_sound_region_is_safe _ _ _ Set.univ (original_scalar_region_postfixed a s Ω A) x (Set.mem_univ x)

def presentLicensedScalar (x : PureVector (KGNRCarrier A)) : LicensedScalarReceiver a s Ω A :=
  let D := originalScalarTask a s Ω A
  presentSafeOriginalUse D.act D.descriptor D.answers
    (originalLocalTest D) (declaredOriginalEdge D) (originalEdgeTest D)
    ⟨x, original_scalar_is_safe a s Ω A x⟩

def licensedScalarPure (r : LicensedScalarReceiver a s Ω A) : PureVector (KGNRCarrier A) := (r.val ()).1.1
def licensedScalarMeaning (r : LicensedScalarReceiver a s Ω A) : OriginalScalarUseMeaning a Ω A := (r.val ()).1.2
def licensedScalarReference (r : LicensedScalarReceiver a s Ω A)
    (q : ScalarUseQuestion a Ω A) : Option KGFamilyReadout := (r.val ()).2 q

theorem present_licensed_scalar_surjective : Function.Surjective (presentLicensedScalar a s Ω A) := by
  intro r
  obtain ⟨x, hx⟩ := r.property
  exact ⟨x.val, Subtype.ext hx⟩

theorem licensed_scalar_meaning_exact (r : LicensedScalarReceiver a s Ω A) :
    licensedScalarMeaning a s Ω A r = originalScalarUseMeaning a s Ω A := by
  obtain ⟨x, rfl⟩ := present_licensed_scalar_surjective a s Ω A r
  rfl

theorem licensed_scalar_reference_square (r : LicensedScalarReceiver a s Ω A)
    (q : ScalarUseQuestion a Ω A) :
    licensedScalarReference a s Ω A r q =
      (kgNRReceivingRegisteredOrbit a s Ω A.shape).references.referenceAt (licensedScalarPure a s Ω A r) q := by
  obtain ⟨x, rfl⟩ := present_licensed_scalar_surjective a s Ω A r
  rfl

def licensedScalarOriginalPure (r : LicensedScalarReceiver a s Ω A) : PureVector (KGFamilyCarrier A.raw) :=
  (licensedScalarMeaning a s Ω A r).originalPreparation (licensedScalarPure a s Ω A r)

def licensedScalarState (r : LicensedScalarReceiver a s Ω A) : PhysicalRay (KGNRCarrier A) :=
  rayMap _ (licensedScalarPure a s Ω A r)

def licensedScalarFullState (r : LicensedScalarReceiver a s Ω A) : PhysicalRay (kgNRFullFamilySpace A.shape) :=
  (licensedScalarMeaning a s Ω A r).fullProjection (licensedScalarState a s Ω A r)

def licensedScalarOutput (r : LicensedScalarReceiver a s Ω A)
    (q : KGNRReceivingQuestion a Ω A.shape) : KGFamilyReadout :=
  (licensedScalarMeaning a s Ω A r).completeOutput (licensedScalarPure a s Ω A r) q

theorem licensed_scalar_state_coverage : Function.Surjective (licensedScalarState a s Ω A) := by
  intro q
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  exact ⟨presentLicensedScalar a s Ω A x, rfl⟩

theorem licensed_scalar_old_reference_square (r : LicensedScalarReceiver a s Ω A)
    (q : RegisteredQuestion (KGFamilyQuestion a Ω A.raw)) :
    licensedScalarReference a s Ω A r (mapRegisteredQuestion kgNROldQuestion q) =
      (kgRawRegisteredOrbit a s Ω A.raw).references.referenceAt (licensedScalarOriginalPure a s Ω A r) q := by
  rw [licensed_scalar_reference_square, licensedScalarOriginalPure, licensed_scalar_meaning_exact]
  exact kg_nr_receiving_old_registered_reference a s Ω A.shape _ q

theorem licensed_scalar_old_complete_record (r : LicensedScalarReceiver a s Ω A)
    (q : KGFamilyQuestion a Ω A.raw) :
    licensedScalarOutput a s Ω A r (kgNROldQuestion q) =
      kgFamilyOutput a s Ω A.raw (licensedScalarOriginalPure a s Ω A r) q := by
  unfold licensedScalarOutput licensedScalarOriginalPure
  rw [licensed_scalar_meaning_exact]
  exact (kg_nr_receiving_old_record a s Ω A.shape _ q).trans
    (kg_spatial_family_complete_original_record a s Ω A.shape _ q)

def licensedScalarContinue (t : ℝ) (r : LicensedScalarReceiver a s Ω A) : LicensedScalarReceiver a s Ω A :=
  presentLicensedScalar a s Ω A (scalarPureFlow a A t (licensedScalarPure a s Ω A r))

theorem licensed_scalar_continuation_reference (t : ℝ) (r : LicensedScalarReceiver a s Ω A)
    (q : ScalarUseQuestion a Ω A) :
    licensedScalarReference a s Ω A (licensedScalarContinue a s Ω A t r) q =
      licensedScalarReference a s Ω A r (mapRegisteredQuestion (kgNRQuestionAdvance t) q) := by
  rw [licensed_scalar_reference_square, licensed_scalar_reference_square]
  exact (kg_nr_receiving_continuation_reference a s t Ω A.shape _ q).symm

theorem licensed_scalar_continuation_first_failure (t : ℝ) (r : LicensedScalarReceiver a s Ω A)
    (word : List (KGNRReceivingQuestion a Ω A.shape)) :
    kgFirstFailure (licensedScalarOutput a s Ω A r) (word.map (kgNRQuestionAdvance t)) =
      kgFirstFailure (licensedScalarOutput a s Ω A (licensedScalarContinue a s Ω A t r)) word := by
  unfold licensedScalarOutput
  rw [licensed_scalar_meaning_exact, licensed_scalar_meaning_exact]
  exact kg_nr_receiving_continuation_first_failure a s t Ω A.shape _ word

theorem licensed_scalar_full_continuation_square (t : ℝ) (r : LicensedScalarReceiver a s Ω A) :
    licensedScalarFullState a s Ω A (licensedScalarContinue a s Ω A t r) =
      unitaryRayMap (kgNRFullFamilyFlow a t A.shape) (licensedScalarFullState a s Ω A r) := by
  unfold licensedScalarFullState
  rw [licensed_scalar_meaning_exact, licensed_scalar_meaning_exact]
  exact kg_nr_full_projection_ray_continuation a t A.shape _

def licensedScalarComparison {B : KGNRObject a} (f : A ⟶ B)
    (r : LicensedScalarReceiver a s Ω A) : LicensedScalarReceiver a s Ω B :=
  presentLicensedScalar a s Ω B (PureVector.mapUnitary f.lift.spatial (licensedScalarPure a s Ω A r))

theorem licensed_scalar_comparison_reference {B : KGNRObject a} (f : A ⟶ B)
    (r : LicensedScalarReceiver a s Ω A) (q : ScalarUseQuestion a Ω B) :
    licensedScalarReference a s Ω A r (mapRegisteredQuestion (kgNRQuestionPullback f.lift) q) =
      licensedScalarReference a s Ω B (licensedScalarComparison a s Ω A f r) q := by
  rw [licensed_scalar_reference_square, licensed_scalar_reference_square]
  exact kg_nr_receiving_comparison_reference a s Ω A.shape B.shape f.lift f.compatible _ q

def licensedScalarRegion {V : Opens CoordinatePoint} (_h : Ω ≤ V)
    (r : LicensedScalarReceiver a s Ω A) : LicensedScalarReceiver a s V A :=
  presentLicensedScalar a s V A (licensedScalarPure a s Ω A r)

theorem licensed_scalar_region_reference {V : Opens CoordinatePoint} (h : Ω ≤ V)
    (r : LicensedScalarReceiver a s Ω A) (q : ScalarUseQuestion a Ω A) :
    licensedScalarReference a s V A (licensedScalarRegion a s Ω A h r)
      (mapRegisteredQuestion (kgNRQuestionExtend h) q) = licensedScalarReference a s Ω A r q := by
  rw [licensed_scalar_reference_square, licensed_scalar_reference_square]
  exact kg_nr_receiving_regional_reference a s h A.shape _ q

def licensedScalarTensor (B : KGNRObject a) (r : LicensedScalarReceiver a s Ω A)
    (t : LicensedScalarReceiver a s Ω B) : LicensedScalarReceiver a s Ω (kgNRTensor A B) :=
  presentLicensedScalar a s Ω (kgNRTensor A B)
    (kgRawTensor (licensedScalarPure a s Ω A r) (licensedScalarPure a s Ω B t))

theorem licensed_scalar_tensor_original_square (B : KGNRObject a)
    (r : LicensedScalarReceiver a s Ω A) (t : LicensedScalarReceiver a s Ω B) :
    licensedScalarOriginalPure a s Ω (kgNRTensor A B) (licensedScalarTensor a s Ω A B r t) =
      kgRawTensor (licensedScalarOriginalPure a s Ω A r) (licensedScalarOriginalPure a s Ω B t) := by
  unfold licensedScalarOriginalPure
  rw [licensed_scalar_meaning_exact, licensed_scalar_meaning_exact, licensed_scalar_meaning_exact]
  exact kg_spatial_family_tensor_original_square a A.shape B.shape _ _

def licensedScalarHamiltonian (r : LicensedScalarReceiver a s Ω A) :=
  kgNRSpatialKinetic (licensedScalarMeaning a s Ω A r).parameters

def licensedScalarFullFlow (r : LicensedScalarReceiver a s Ω A) :=
  kgNRSpatialFreeFlow (licensedScalarMeaning a s Ω A r).parameters

theorem licensed_scalar_domain_graph_receipt (r : LicensedScalarReceiver a s Ω A) :
    (↑(licensedScalarHamiltonian a s Ω A r).domain : Set KGNRSpatialHilbert) =
      (licensedScalarMeaning a s Ω A r).fullKineticDomain ∧
    (↑(licensedScalarHamiltonian a s Ω A r).graph : Set (KGNRSpatialHilbert × KGNRSpatialHilbert)) =
      (licensedScalarMeaning a s Ω A r).fullKineticGraph := by
  unfold licensedScalarHamiltonian
  rw [licensed_scalar_meaning_exact]
  exact ⟨rfl, rfl⟩

theorem licensed_scalar_full_flow_receipt (r : LicensedScalarReceiver a s Ω A)
    (t : ℝ) (f : KGNRSpatialHilbert) :
    licensedScalarFullFlow a s Ω A r t f = (licensedScalarMeaning a s Ω A r).fullScalarEvolution t f := by
  unfold licensedScalarFullFlow
  rw [licensed_scalar_meaning_exact]
  rfl

theorem licensed_scalar_exact_generator (r : LicensedScalarReceiver a s Ω A) :
    GlobalCharge.ExactGenerator (Translation.coefficient (licensedScalarMeaning a s Ω A r).parameters.hbar)
      (licensedScalarFullFlow a s Ω A r) (licensedScalarHamiltonian a s Ω A r) := by
  unfold licensedScalarFullFlow licensedScalarHamiltonian
  rw [licensed_scalar_meaning_exact]
  exact kg_nr_spatial_exact_generator a

theorem licensed_scalar_complete_weak_graph (r : LicensedScalarReceiver a s Ω A)
    (f g : KGNRSpatialHilbert) :
    (f, g) ∈ (licensedScalarHamiltonian a s Ω A r).graph ↔
      ∀ test : 𝓢(KGSpatialSpace, ℂ), (g : KGSpatialDistribution) test =
        (f : KGSpatialDistribution) (kgNRSpatialTestResponse a test) := by
  unfold licensedScalarHamiltonian
  rw [licensed_scalar_meaning_exact]
  exact kg_nr_spatial_kinetic_test_graph a f g

theorem licensed_scalar_calibrated_comparator (r : LicensedScalarReceiver a s Ω A)
    {H : LinearPMap ℂ KGNRSpatialHilbert KGNRSpatialHilbert} (C : KGScalarFreeComparator H)
    (calibration : KGFreeAnchoredDispersionAt a C) : H = licensedScalarHamiltonian a s Ω A r := by
  unfold licensedScalarHamiltonian
  rw [licensed_scalar_meaning_exact]
  exact kg_free_calibrated_comparator_eq a C calibration

end AASCKleinGordon.CanonicalLicensing
