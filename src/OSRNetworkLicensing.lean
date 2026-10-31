import OSRNetworkSource

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCMetricityOriginalAssembly AASCMetricityLicensingConstruction
namespace AASCKleinGordon.OperationalSR
open KGQuantum W9 TopologicalSpace AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
variable (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint) (n : ℕ)

def networkRebase (h : Fin (n+1) → ℝ) (x : NetworkSource a s Omega n) : NetworkSource a s Omega n :=
  {x with epoch := fun i => x.epoch i+h i}

theorem network_rebase_preserves_complete_profile (h : Fin (n+1) → ℝ) (x : NetworkSource a s Omega n) :
    networkCompleteObserve a s Omega n (networkRebase a s Omega n h x)=networkCompleteObserve a s Omega n x := by
  funext q
  rw [network_complete_profile_factors_physical_data,network_complete_profile_factors_physical_data]
  rfl

theorem network_data_operation_preserves_sound (op : NetworkOperation n) (d e : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (step : networkDataOperation a s Omega n op d=some e) :
    networkSound a s Omega n e := by
  cases op with
  | rebase i h =>
    simp only [networkDataOperation,Option.some.injEq] at step
    subst e
    exact sound
  | scalarContinue t =>
    simp only [networkDataOperation,Option.some.injEq] at step
    subst e
    exact sound
  | extend delta =>
    by_cases forward : 0 ≤ delta
    · simp only [networkDataOperation,if_pos forward,Option.some.injEq] at step
      subst e
      exact ⟨sound.1,sound.2.1,by dsimp;linarith [sound.2.2]⟩
    · simp [networkDataOperation,forward] at step
  | restrict lo hi =>
    by_cases contained : d.lo ≤ lo ∧ lo ≤ hi ∧ hi ≤ d.hi
    · simp only [networkDataOperation,if_pos contained,Option.some.injEq] at step
      subst e
      exact ⟨sound.1,sound.2.1,contained.2.1⟩
    · simp [networkDataOperation,contained] at step
  | certifyRadar index correction =>
    by_cases domain : requestDomain a s Omega n d index correction
    · simp only [networkDataOperation,if_pos domain,Option.some.injEq] at step
      subst e
      exact sound
    · simp [networkDataOperation,domain] at step
  | certifyRuler i j T =>
    by_cases domain : rulerDomain a s Omega n d i j T
    · simp only [networkDataOperation,if_pos domain,Option.some.injEq] at step
      subst e
      exact sound
    · simp [networkDataOperation,domain] at step
  | advance delta =>
    by_cases forward : 0 ≤ delta
    · simp only [networkDataOperation,if_pos forward,Option.some.injEq] at step
      subst e
      exact sound
    · simp [networkDataOperation,forward] at step
  | certifyMeasuring Q i j =>
    by_cases domain : measuringDomain a s Omega n d Q i j
    · simp only [networkDataOperation,if_pos domain,Option.some.injEq] at step
      subst e
      exact sound
    · simp [networkDataOperation,domain] at step

theorem network_operation_preserves_actual_sound_region (op : NetworkOperation n)
    (x y : NetworkSource a s Omega n) (sound : networkSound a s Omega n x.data)
    (step : networkOperation a s Omega n op x=some y) : networkSound a s Omega n y.data := by
  have square := network_operation_actual_data_square a s Omega n op x
  rw [step,Option.map_some] at square
  exact network_data_operation_preserves_sound a s Omega n op x.data y.data sound square.symm

abbrev NetworkContext := SRContextQuery (NetworkQuestion n) (NetworkOperation n)
abbrev NetworkContextValue := srContextValue (Op:=NetworkOperation n) (networkValue a s Omega n)
abbrev NetworkProfile := (q : NetworkContext n) → NetworkContextValue a s Omega n q

structure NetworkMeaning where
  massParameter : ℝ
  actualGeometry : QuadraticForm ℝ SREvent
  observations : NetworkSource a s Omega n → NetworkProfile a s Omega n
  operations : NetworkOperation n → NetworkSource a s Omega n → Option (NetworkSource a s Omega n)

def networkMeaning : NetworkMeaning a s Omega n :=
  ⟨a.mass,srOriginalOrderQuadratic,networkCompleteObserve a s Omega n,networkOperation a s Omega n⟩

def networkOriginalAnswer (ground : NetworkProfile a s Omega n) :
    (q : Unit ⊕ NetworkContext n) → ProfileValue (NetworkContextValue a s Omega n) (NetworkMeaning a s Omega n) q → Prop
  | .inl _ => fun meaning => meaning=networkMeaning a s Omega n
  | .inr q => fun answer => answer=ground q

def networkTask : OriginalMetricTask (NetworkSource a s Omega n) (NetworkSource a s Omega n)
    (NetworkProfile a s Omega n) (NetworkMeaning a s Omega n) (Fin (n+1) → ℝ) (NetworkOperation n)
    (NetworkContext n) (NetworkContextValue a s Omega n) (NetworkSource a s Omega n)
    (NetworkMeaning a s Omega n) (NetworkMeaning a s Omega n) (NetworkProfile a s Omega n) where
  act := id
  ground := networkCompleteObserve a s Omega n
  descriptor := fun _ => networkMeaning a s Omega n
  descriptorMeaning := id
  answers := networkCompleteObserve a s Omega n
  qualification := fun ground x => networkCompleteObserve a s Omega n x=ground ∧ networkSound a s Omega n x.data
  originalAnswer := networkOriginalAnswer a s Omega n
  originalLocal := fun x => networkSound a s Omega n x.data
  redescription := fun x y => ∃ h, y=networkRebase a s Omega n h x
  redEdge := fun x h y => y=networkRebase a s Omega n h x
  contEdge := fun x op y => networkOperation a s Omega n op x=some y
  redOriginalWarrant := fun x h y => y=networkRebase a s Omega n h x
  contOriginalWarrant := fun x op y => networkOperation a s Omega n op x=some y ∧ networkSound a s Omega n y.data
  context := fun _ => networkMeaning a s Omega n
  boundaryWork := id

theorem network_actual_source_passes_local_tests (x : NetworkSource a s Omega n)
    (sound : networkSound a s Omega n x.data) : originalLocalTest (networkTask a s Omega n) x := by
  refine ⟨⟨x,rfl,sound⟩,?_,sound,?_⟩
  · intro q
    cases q <;> rfl
  · intro y same
    obtain ⟨h,hh⟩ := same
    exact ⟨h,y,hh,rfl⟩

def networkSoundRegion : Set (NetworkSource a s Omega n) := {x | networkSound a s Omega n x.data}

theorem network_actual_sound_region_postfixed :
    networkSoundRegion a s Omega n ⊆ originalSafetyOperator (networkTask a s Omega n) (networkSoundRegion a s Omega n) := by
  intro x sound
  refine ⟨network_actual_source_passes_local_tests a s Omega n x sound,?_⟩
  intro t y edge
  cases t with
  | inl h =>
    change y=networkRebase a s Omega n h x at edge
    subst y
    exact ⟨⟨rfl,network_rebase_preserves_complete_profile a s Omega n h x⟩,sound⟩
  | inr op =>
    have next := network_operation_preserves_actual_sound_region a s Omega n op x y sound edge
    exact ⟨⟨edge,next⟩,next⟩

theorem actual_network_source_has_kernel_faithful_license (x : NetworkSource a s Omega n)
    (sound : networkSound a s Omega n x.data) :
    constructedLicensing (networkTask a s Omega n) x (networkMeaning a s Omega n) :=
  canonical_licensing_contains_every_original_sound_region _ (networkSoundRegion a s Omega n)
    (network_actual_sound_region_postfixed a s Omega n) x sound

abbrev LicensedNetworkReceiver :=
  let D := networkTask a s Omega n
  CanonicalLicensingReceiver D.act D.descriptor D.answers
    (originalLocalTest D) (declaredOriginalEdge D) (originalEdgeTest D)

def presentLicensedNetwork (x : NetworkSource a s Omega n) (sound : networkSound a s Omega n x.data) :
    LicensedNetworkReceiver a s Omega n :=
  let D := networkTask a s Omega n
  presentSafeOriginalUse D.act D.descriptor D.answers
    (originalLocalTest D) (declaredOriginalEdge D) (originalEdgeTest D)
    ⟨x,original_sound_region_is_safe _ _ _ (networkSoundRegion a s Omega n)
      (network_actual_sound_region_postfixed a s Omega n) x sound⟩

def licensedNetworkSource (r : LicensedNetworkReceiver a s Omega n) : NetworkSource a s Omega n :=
  (r.val ()).1.1

theorem licensed_network_has_actual_sound_source (r : LicensedNetworkReceiver a s Omega n) :
    networkSound a s Omega n (licensedNetworkSource a s Omega n r).data := by
  obtain ⟨x,hx⟩ := r.property
  have safe : x.val ∈ canonicalSafeUses (networkTask a s Omega n) := x.property
  rw [original_safe_uses_are_fixed] at safe
  have sound : networkSound a s Omega n x.val.data := safe.1.2.2.1
  have same : licensedNetworkSource a s Omega n r=x.val :=
    (congrArg (fun p => (p ()).1.1) hx).symm
  rw [same]
  exact sound

def licensedNetworkToOld (r : LicensedNetworkReceiver a s Omega n) (i : Fin (n+1)) : LicensedJointSRReceiver a s Omega :=
  licensedNetworkSite a s Omega n (licensedNetworkSource a s Omega n r)
    (licensed_network_has_actual_sound_source a s Omega n r) i

theorem licensed_network_old_actual_raw_source_square (x : NetworkSource a s Omega n)
    (sound : networkSound a s Omega n x.data) (i : Fin (n+1)) :
    licensedJointSRSource a s Omega (licensedNetworkToOld a s Omega n (presentLicensedNetwork a s Omega n x sound) i)=
      networkRawJoint a s Omega n x i := rfl

theorem licensed_network_old_preparations_square (r : LicensedNetworkReceiver a s Omega n) (i : Fin (n+1)) :
    licensedSRScalar a s Omega (licensedNetworkToOld a s Omega n r i)=(licensedNetworkSource a s Omega n r).data.scalar ∧
    (licensedJointSRSource a s Omega (licensedNetworkToOld a s Omega n r i)).metric=(licensedNetworkSource a s Omega n r).data.metric :=
  ⟨rfl,rfl⟩

end AASCKleinGordon.OperationalSR
