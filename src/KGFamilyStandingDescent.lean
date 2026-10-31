import KGFamilyRecordLaws
import RegisteredOrbitStandingDescent
import KGComparisonCoherence
import Mathlib.Topology.Category.TopCat.Basic

/-! Concrete registration and the W9 registered-standing descent for the KG
family. The scalar quotient is reused, never replaced by a profile quotient.
The original-source comparison is proved after universal standing descent. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 CategoryTheory TopologicalSpace AASCSemanticExhaustion
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

def kgRawRegisteredOrbit (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) :
    RawRegisteredOrbit (PureVector (KGFamilyCarrier A)) (KGFamilyQuestion a Ω A)
      KGFamilyReadout (PhysicalRay (KGFamilyCarrier A)) where
  output := kgFamilyOutput a s Ω A
  succeeds := kgFamilySuccess
  weight := transitionProbability
  outgoing := KGFamilyQuestion.comparison
  incoming := KGFamilyQuestion.reverseComparison
  probabilityValue := KGFamilyReadout.comparison
  probability_injective := by intro r t h;exact KGFamilyReadout.comparison.inj h
  outgoing_output _ _ := rfl
  incoming_output _ _ := rfl
  probability_success _ := rfl
  orbit := PureVector.ScalarRel
  phase_output x y h π := by
    obtain ⟨c,hc,h⟩ := h
    have equal : PureVector.smul c hc x=y := Subtype.ext h
    rw [← equal]
    exact (kg_family_output_scalar a s Ω A c hc x π).symm
  raw_profiles_exact x y := (kg_raw_profiles_exact_orbits x y).trans
    (rayMap_eq_iff (KGFamilyCarrier A) x y)
  q := rayMap (KGFamilyCarrier A)
  q_surjective r := by induction r using Quotient.inductionOn with | _ x => exact ⟨x,rfl⟩
  q_fibres := rayMap_eq_iff (KGFamilyCarrier A)
  coequalizer f hf := kg_raw_orbit_coequalizer f hf

theorem kg_family_raw_nonempty (a : Parameters) (A : KGFamilyObject a) :
    Nonempty (PureVector (KGFamilyCarrier A)) := kg_raw_comparison_nonempty a A.shape

theorem kg_raw_registered_probability (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (x y : PureVector (KGFamilyCarrier A)) :
    (kgRawRegisteredOrbit a s Ω A).kernel.standing x
      (.execution (.comparison y)) (.comparison (transitionProbability x y)) :=
  (kgRawRegisteredOrbit a s Ω A).raw_probability_standing x y

theorem kg_registered_orbit_exact (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (x y : PureVector (KGFamilyCarrier A)) :
    (kgRawRegisteredOrbit a s Ω A).SameRegisteredStanding x y ↔
      rayMap (KGFamilyCarrier A) x=rayMap (KGFamilyCarrier A) y :=
  (kgRawRegisteredOrbit a s Ω A).registered_standing_exact x y

def kgW9StandingRecord (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) : PhysicalRay (KGFamilyCarrier A) → KGFamilyQuestion a Ω A → KGFamilyReadout :=
  (kgRawRegisteredOrbit a s Ω A).standingRecord

theorem kg_w9_standing_complete_record (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (x : PureVector (KGFamilyCarrier A)) (π : KGFamilyQuestion a Ω A) :
    kgW9StandingRecord a s Ω A (rayMap _ x) π=kgFamilyOutput a s Ω A x π :=
  (kgRawRegisteredOrbit a s Ω A).standing_record_spec x π

theorem kg_w9_standing_record_faithful (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) : Function.Injective (kgW9StandingRecord a s Ω A) :=
  (kgRawRegisteredOrbit a s Ω A).standing_record_injective

theorem kg_continuous_universal_standing (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) {Y : Type} [TopologicalSpace Y]
    (f : PureVector (KGFamilyCarrier A) → Y) (continuous : Continuous f)
    (standing : ∀ x y,(kgRawRegisteredOrbit a s Ω A).SameRegisteredStanding x y → f x=f y) :
    ∃! g : PhysicalRay (KGFamilyCarrier A) → Y,Continuous g ∧ ∀ x,g (rayMap _ x)=f x := by
  apply kg_raw_continuous_orbit_coequalizer f continuous
  intro x y h
  exact standing x y ((kg_registered_orbit_exact a s Ω A x y).mpr
    ((rayMap_eq_iff (KGFamilyCarrier A) x y).mpr h))

theorem kg_identity_context_raw_output (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (x : PureVector (fockCoreDomain a)) (π : WickMetricPathRoleProtocol Ω) :
    kgFamilyOutput a s Ω (kgOriginalObject a) x (.original .original π)=
      .extraction (some (wickMetricPathRoleOutput a s Ω ((kgRawOriginalEquiv a).symm x) π)) := by
  simpa only [Equiv.apply_symm_apply] using
    kg_family_original_identity a s Ω ((kgRawOriginalEquiv a).symm x) π

def kgRawOriginalResponse (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (x : PureVector (fockCoreDomain a)) : WickMetricPathQresp a s Ω :=
  Quotient.mk (wickMetricPathRoleSetoid a s Ω) ((kgRawOriginalEquiv a).symm x)

theorem kg_raw_original_response_registered (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (x y : PureVector (fockCoreDomain a))
    (same : (kgRawRegisteredOrbit a s Ω (kgOriginalObject a)).SameRegisteredStanding x y) :
    kgRawOriginalResponse a s Ω x=kgRawOriginalResponse a s Ω y := by
  apply Quotient.sound
  intro π
  have record := ((kgRawRegisteredOrbit a s Ω (kgOriginalObject a)).same_record_iff_registered x y).mpr same
  have eq := record (.original .original π)
  change kgFamilyOutput a s Ω (kgOriginalObject a) x (.original .original π)=
    kgFamilyOutput a s Ω (kgOriginalObject a) y (.original .original π) at eq
  rw [kg_identity_context_raw_output,kg_identity_context_raw_output] at eq
  exact Option.some.inj (KGFamilyReadout.extraction.inj eq)

/-- Obtained from the derived universal standing descent on the complete
registered family; no original-source equality is accepted as input. -/
def kgW9OriginalResponse (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    PhysicalRay (fockCoreDomain a) → WickMetricPathQresp a s Ω :=
  ((kgRawRegisteredOrbit a s Ω (kgOriginalObject a)).universal_standing_descent
    (kgRawOriginalResponse a s Ω) (kg_raw_original_response_registered a s Ω)).choose

theorem kg_w9_original_response_spec (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (x : PureVector (fockCoreDomain a)) :
    kgW9OriginalResponse a s Ω (rayMap _ x)=kgRawOriginalResponse a s Ω x :=
  ((kgRawRegisteredOrbit a s Ω (kgOriginalObject a)).universal_standing_descent
    (kgRawOriginalResponse a s Ω) (kg_raw_original_response_registered a s Ω)).choose_spec.1 x

theorem kg_w9_original_response_comparison (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (r : PhysicalRay (fockCoreDomain a)) :
    kgW9OriginalResponse a s Ω r=kgOriginalQuantumRecord a s Ω r := by
  induction r using Quotient.inductionOn with
  | _ x =>
    refine (kg_w9_original_response_spec a s Ω x).trans ?_
    have eq := kg_original_quantum_record_on_representatives a s Ω ((kgRawOriginalEquiv a).symm x)
    simpa only [Equiv.apply_symm_apply] using eq.symm

theorem kg_w9_complete_original_source_square (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (r : PhysicalRay (fockCoreDomain a)) :
    kgW9OriginalResponse a s Ω r=
      (wickMetricPathF a s Ω (wickMetricPathPiA a s Ω
        (wickCommonRoleSourcePresentation a s Ω (kgOriginalQuantumToRay a r)))).val :=
  (kg_w9_original_response_comparison a s Ω r).trans (kg_original_quantum_source_square a s Ω r)

end AASCKleinGordon
