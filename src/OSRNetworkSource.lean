import OSRClockLicensedSource
import OSRProtocolDomains
import OSRMeasuringHyperplane

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR
open KGQuantum W9 TopologicalSpace AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

structure ExchangeRequest (n : ℕ) where
  fromSite : Fin (n+1)
  toSite : Fin (n+1)
  emit : ℝ
  delay : ℝ
  energy : ℝ

structure NetworkData (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint) (n : ℕ) where
  sites : SiteData n
  frame : SRMatrixFrame
  origin : SREvent
  lo : ℝ
  hi : ℝ
  reference : ℝ
  region : Set SREvent
  schedule : List (ExchangeRequest n)
  clockResource : Fin (n+1) → Bool
  signalResource : ℕ → Bool
  relayResource : ℕ → Bool
  scalar : LicensedScalarReceiver a s Omega (scalarBaseObject a)
  metric : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega}

structure NetworkSource (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint) (n : ℕ) where
  data : NetworkData a s Omega n
  epoch : Fin (n+1) → ℝ

variable (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint) (n : ℕ)

def networkSound (d : NetworkData a s Omega n) : Prop :=
  (∀ i, 0 < a.mass+d.sites.internalEnergy i) ∧ d.frame ∈ srNativeFrameComparisons ∧ d.lo ≤ d.hi

def networkBaseJoint (d : NetworkData a s Omega n) (i : Fin (n+1)) : JointOriginalSource a s Omega :=
  ⟨srPassiveClockUse a.mass d.frame d.origin (siteUse a.mass d.sites i d.lo d.hi),d.scalar,d.metric⟩

def networkRawJoint (x : NetworkSource a s Omega n) (i : Fin (n+1)) : JointOriginalSource a s Omega :=
  jointClockRebase a s Omega (observerSlope x.data.frame*x.epoch i) (networkBaseJoint a s Omega n x.data i)

theorem network_base_joint_actually_valid (d : NetworkData a s Omega n) (sound : networkSound a s Omega n d)
    (i : Fin (n+1)) : srNativeClockUseValid a.mass (networkBaseJoint a s Omega n d i).clock :=
  (sr_passive_clock_use_has_exact_original_eligibility a.mass a.mass_pos (srNativeOccupiedFrameSource a.mass a.mass_pos)
    d.frame sound.2.1 d.origin _).mpr (site_use_actually_valid a.mass d.sites i (sound.1 i) d.lo d.hi sound.2.2)

theorem network_raw_joint_actually_valid (x : NetworkSource a s Omega n)
    (sound : networkSound a s Omega n x.data) (i : Fin (n+1)) :
    srNativeClockUseValid a.mass (networkRawJoint a s Omega n x i).clock :=
  (joint_clock_rebase_preserves_validity a s Omega (observerSlope x.data.frame*x.epoch i) _).mpr
    (network_base_joint_actually_valid a s Omega n x.data sound i)

def licensedNetworkSite (x : NetworkSource a s Omega n)
    (sound : networkSound a s Omega n x.data) (i : Fin (n+1)) : LicensedJointSRReceiver a s Omega :=
  presentLicensedJointSR a s Omega (networkRawJoint a s Omega n x i)
    (network_raw_joint_actually_valid a s Omega n x sound i)

theorem network_licensed_site_retains_actual_raw_source (x : NetworkSource a s Omega n)
    (sound : networkSound a s Omega n x.data) (i : Fin (n+1)) :
    licensedJointSRSource a s Omega (licensedNetworkSite a s Omega n x sound i)=networkRawJoint a s Omega n x i := rfl

def requestRelay (d : NetworkData a s Omega n) (r : ExchangeRequest n) : RelayData :=
  relayAtSites d.sites r.fromSite r.toSite r.emit r.delay r.energy

def requestDomain (d : NetworkData a s Omega n) (index : ℕ) (correction : ℝ) : Prop :=
  ∃ r, d.schedule[index]?=some r ∧ d.clockResource r.fromSite=true ∧ d.clockResource r.toSite=true ∧
    d.signalResource index=true ∧ (r.delay=0 ∨ d.relayResource index=true) ∧
    d.sites.position r.toSite ≠ d.sites.position r.fromSite ∧ 0 < r.energy ∧ 0 ≤ r.delay ∧
    correction=r.delay ∧
    (r.delay=0 ∨ segmentCovered d.region
      (frameEvent d.frame d.origin (d.lo,relayZ (requestRelay a s Omega n d r)))
      (frameEvent d.frame d.origin (d.hi,relayZ (requestRelay a s Omega n d r)))) ∧ d.lo ≤ r.emit ∧ (relayReturn (requestRelay a s Omega n d r)).1 ≤ d.hi ∧
    relayCovered (frameInverse d.frame d.origin '' d.region) (requestRelay a s Omega n d r) ∧
    (∀ i, segmentCovered d.region (frameEvent d.frame d.origin (d.lo,d.sites.position i))
      (frameEvent d.frame d.origin (d.hi,d.sites.position i)))

structure RadarAnswer where
  mainIdentity : ℕ
  events : List SREvent
  readings : ℝ × ℝ × ℝ × ℝ
  offset : ℝ
  length : ℝ

def actualRadarAnswer (d : NetworkData a s Omega n) (index : ℕ) (r : ExchangeRequest n) : RadarAnswer :=
  let R := requestRelay a s Omega n d r
  let tm := siteReading a.mass d.sites r.fromSite (relayDeparture R).1
  let ta := siteReading a.mass d.sites r.toSite (relayArrival R).1
  let td := siteReading a.mass d.sites r.toSite (relayRelease R).1
  let tp := siteReading a.mass d.sites r.fromSite (relayReturn R).1
  ⟨index,[relayDeparture R,relayArrival R,relayTurn R,relayRelease R,relayReturn R].map (frameEvent d.frame d.origin),
    (tm,ta,td,tp),ta-(tm+tp-r.delay)/2,(tp-tm-r.delay)/2⟩

def radarRead (d : NetworkData a s Omega n) (index : ℕ) (correction : ℝ) : Option RadarAnswer :=
  if requestDomain a s Omega n d index correction then
    (d.schedule[index]?).map (actualRadarAnswer a s Omega n d index) else none

theorem radar_read_exact_domain (d : NetworkData a s Omega n) (index : ℕ) (correction : ℝ) :
    (radarRead a s Omega n d index correction).isSome=true ↔ requestDomain a s Omega n d index correction := by
  by_cases domain : requestDomain a s Omega n d index correction
  · have saved := domain
    obtain ⟨r,registered,_⟩ := domain
    simp [radarRead,saved,registered]
  · simp [radarRead,domain]

theorem occupied_network_radar_answer (d : NetworkData a s Omega n) (sound : networkSound a s Omega n d)
    (index : ℕ) (r : ExchangeRequest n) :
    (actualRadarAnswer a s Omega n d index r).offset=d.sites.phase r.toSite-d.sites.phase r.fromSite ∧
    (actualRadarAnswer a s Omega n d index r).length=‖d.sites.position r.toSite-d.sites.position r.fromSite‖ := by
  have answer := occupied_radar_readings a.mass d.sites r.fromSite r.toSite
    (sound.1 r.fromSite) (sound.1 r.toSite) r.emit r.delay r.energy
  exact ⟨answer.1,answer.2.2⟩

def measuringDomain (d : NetworkData a s Omega n) (Q : MeasuringQuery) (i j : Fin (n+1)) : Prop :=
  Q.frame ∈ srNativeFrameComparisons ∧
  d.clockResource i=true ∧ d.clockResource j=true ∧ d.sites.position j ≠ d.sites.position i ∧
  d.lo ≤ measuringSiteTime Q (d.sites.position i) ∧ measuringSiteTime Q (d.sites.position i) ≤ d.hi ∧
  d.lo ≤ measuringSiteTime Q (d.sites.position j) ∧ measuringSiteTime Q (d.sites.position j) ≤ d.hi ∧
  segmentCovered d.region (frameEvent d.frame d.origin (d.lo,d.sites.position i))
    (frameEvent d.frame d.origin (d.hi,d.sites.position i)) ∧
  segmentCovered d.region (frameEvent d.frame d.origin (d.lo,d.sites.position j))
    (frameEvent d.frame d.origin (d.hi,d.sites.position j))

def rulerDomain (d : NetworkData a s Omega n) (i j : Fin (n+1)) (T : ℝ) : Prop :=
  measuringDomain a s Omega n d ⟨d.frame,d.origin,T⟩ i j

structure MeasuringAnswer where
  firstEvent : SREvent
  secondEvent : SREvent
  firstMeasuredEvent : SREvent
  secondMeasuredEvent : SREvent
  firstReading : ℝ
  secondReading : ℝ
  length : ℝ

def actualMeasuringAnswer (d : NetworkData a s Omega n) (Q : MeasuringQuery) (i j : Fin (n+1)) : MeasuringAnswer :=
  let u := measuringSiteTime Q (d.sites.position i)
  let v := measuringSiteTime Q (d.sites.position j)
  let X := frameEvent Q.frame Q.origin (u,d.sites.position i)
  let Y := frameEvent Q.frame Q.origin (v,d.sites.position j)
  ⟨frameEvent d.frame d.origin (u,d.sites.position i),frameEvent d.frame d.origin (v,d.sites.position j),
    X,Y,siteReading a.mass d.sites i u,siteReading a.mass d.sites j v,‖Y.2-X.2‖⟩

def measuringRead (d : NetworkData a s Omega n) (Q : MeasuringQuery) (i j : Fin (n+1)) : Option MeasuringAnswer :=
  if measuringDomain a s Omega n d Q i j then some (actualMeasuringAnswer a s Omega n d Q i j) else none

def rulerRead (d : NetworkData a s Omega n) (i j : Fin (n+1)) (T : ℝ) : Option (SREvent × SREvent × ℝ) :=
  if rulerDomain a s Omega n d i j T then
    let X := measuredEndpoint d.frame d.origin T (d.sites.position i)
    let Y := measuredEndpoint d.frame d.origin T (d.sites.position j)
    some (X,Y,‖Y.2-X.2‖) else none

structure SignalLedger where
  mainIdentity : ℕ
  compensatorIdentity : ℕ
  mainEvent : SREvent
  mainMomentum : SREvent
  compensatorEvent : SREvent
  compensatorMomentum : SREvent

def signalLedger (d : NetworkData a s Omega n) (index : ℕ) (r : ExchangeRequest n) (T : ℝ) : SignalLedger :=
  let R := requestRelay a s Omega n d r
  ⟨index,index,frameEvent d.frame d.origin (T,relayMainPosition R T),
    srMatrixFrameEventLinear d.frame (relayMainMomentum R T),
    frameEvent d.frame d.origin (T,relayCompensatorPosition R T),
    srMatrixFrameEventLinear d.frame (srNativePositiveRayMomentum r.energy
      (if T ≤ (relayTurn R).1 then -R.direction else R.direction))⟩

def relayClockRecord (d : NetworkData a s Omega n) (r : ExchangeRequest n) : SRClockRecord :=
  srPassiveClockRecord a.mass d.frame d.origin
    (0,0,srNativeRestClock (relayZ (requestRelay a s Omega n d r)))

theorem relay_extra_endpoint_is_actual_positive_clock (d : NetworkData a s Omega n) (r : ExchangeRequest n) :
    0 < srNativeClockMass a.mass (srNativeRestClock (relayZ (requestRelay a s Omega n d r))) ∧
    ∀ T : ℝ, (srNativeClockCoastFlow a.mass T
      (srNativeRestClock (relayZ (requestRelay a s Omega n d r)))).reading=T := by
  refine ⟨(sr_native_positive_rest_clock_is_occupied a.mass a.mass_pos _).1,?_⟩
  intro T
  exact (sr_native_rest_clock_actual_coasting_record a.mass a.mass_pos _ T).2.1

inductive NetworkOperation (n : ℕ)
  | rebase : Fin (n+1) → ℝ → NetworkOperation n
  | scalarContinue : ℝ → NetworkOperation n
  | extend : ℝ → NetworkOperation n
  | restrict : ℝ → ℝ → NetworkOperation n
  | certifyRadar : ℕ → ℝ → NetworkOperation n
  | certifyRuler : Fin (n+1) → Fin (n+1) → ℝ → NetworkOperation n
  | advance : ℝ → NetworkOperation n
  | certifyMeasuring : MeasuringQuery → Fin (n+1) → Fin (n+1) → NetworkOperation n

def networkDataOperation (op : NetworkOperation n) (d : NetworkData a s Omega n) : Option (NetworkData a s Omega n) :=
  match op with
  | .rebase _ _ => some d
  | .scalarContinue t => some {d with scalar := licensedScalarContinue a s Omega (scalarBaseObject a) t d.scalar}
  | .extend delta => if 0 ≤ delta then some {d with hi := d.hi+delta} else none
  | .restrict lo hi => if d.lo ≤ lo ∧ lo ≤ hi ∧ hi ≤ d.hi then some {d with lo := lo,hi := hi} else none
  | .certifyRadar index correction => if requestDomain a s Omega n d index correction then some d else none
  | .certifyRuler i j T => if rulerDomain a s Omega n d i j T then some d else none
  | .advance delta => if 0 ≤ delta then some {d with reference := d.reference+delta} else none
  | .certifyMeasuring Q i j => if measuringDomain a s Omega n d Q i j then some d else none

def networkOperation (op : NetworkOperation n) (x : NetworkSource a s Omega n) : Option (NetworkSource a s Omega n) :=
  match op with
  | .rebase i h => some {x with epoch := fun j => if j=i then x.epoch j+h else x.epoch j}
  | _ => (networkDataOperation a s Omega n op x.data).map (fun d => {x with data := d})

theorem network_operation_actual_data_square (op : NetworkOperation n) (x : NetworkSource a s Omega n) :
    (networkOperation a s Omega n op x).map NetworkSource.data=networkDataOperation a s Omega n op x.data := by
  cases op <;> simp [networkOperation,networkDataOperation,Option.map_map,Function.comp_def]

inductive NetworkQuestion (n : ℕ)
  | old : Fin (n+1) → JointContext → NetworkQuestion n
  | siteEvent : Fin (n+1) → ℝ → NetworkQuestion n
  | siteReading : Fin (n+1) → ℝ → NetworkQuestion n
  | radar : ℕ → ℝ → NetworkQuestion n
  | ruler : Fin (n+1) → Fin (n+1) → ℝ → NetworkQuestion n
  | referenceSelection : NetworkQuestion n
  | protocolContext : NetworkQuestion n
  | signal : ℕ → ℝ → NetworkQuestion n
  | relayEndpoint : ℕ → ℝ → NetworkQuestion n
  | measuring : MeasuringQuery → Fin (n+1) → Fin (n+1) → NetworkQuestion n

def networkValue : NetworkQuestion n → Type
  | .old _ q => JointContextValue a s Omega q
  | .siteEvent _ _ => SREvent
  | .siteReading _ _ => ℝ
  | .radar _ _ => Option RadarAnswer
  | .ruler _ _ _ => Option (SREvent × SREvent × ℝ)
  | .referenceSelection => ℝ × Bool
  | .protocolContext => List (ExchangeRequest n) × (Fin (n+1) → Bool) × (ℕ → Bool) × (ℕ → Bool)
  | .signal _ _ => Option SignalLedger
  | .relayEndpoint _ _ => Option (ℕ × (Fin 2 × SRNativeClockState SRSpace))
  | .measuring _ _ _ => Option MeasuringAnswer

def networkDataObserve (d : NetworkData a s Omega n) : (q : NetworkQuestion n) → networkValue a s Omega n q
  | .old i q => jointCompleteObserve a s Omega (networkBaseJoint a s Omega n d i) q
  | .siteEvent i t => frameEvent d.frame d.origin (t,d.sites.position i)
  | .siteReading i t => siteReading a.mass d.sites i t
  | .radar index correction => radarRead a s Omega n d index correction
  | .ruler i j T => rulerRead a s Omega n d i j T
  | .referenceSelection => (d.reference,decide (d.lo ≤ d.reference ∧ d.reference ≤ d.hi))
  | .protocolContext => (d.schedule,d.clockResource,d.signalResource,d.relayResource)
  | .signal index T => if d.signalResource index=true then
      (d.schedule[index]?).map (fun r => signalLedger a s Omega n d index r T) else none
  | .relayEndpoint index T => (d.schedule[index]?).bind (fun r =>
      if 0 < r.delay ∧ d.relayResource index=true then
        some (index,srNativeCoastingMarkedRecord a.mass (relayClockRecord a s Omega n d r)
          (srPassiveMarkedTime a.mass d.frame d.origin
            (0,0,srNativeRestClock (relayZ (requestRelay a s Omega n d r))) T)) else none)

  | .measuring Q i j => measuringRead a s Omega n d Q i j

def networkOriginalObserve (x : NetworkSource a s Omega n) : (q : NetworkQuestion n) → networkValue a s Omega n q :=
  networkDataObserve a s Omega n x.data

abbrev networkCompleteObserve := srCompleteOriginalContextObserve (networkOriginalObserve a s Omega n) (networkOperation a s Omega n)
abbrev networkDataCompleteObserve := srCompleteOriginalContextObserve (networkDataObserve a s Omega n) (networkDataOperation a s Omega n)
abbrev NetworkReceiver := ContextualQuotient.CanonicalQuotient (networkCompleteObserve a s Omega n)
def presentNetwork := ContextualQuotient.classify (networkCompleteObserve a s Omega n)

theorem network_complete_profile_factors_physical_data (x : NetworkSource a s Omega n)
    (q : SRContextQuery (NetworkQuestion n) (NetworkOperation n)) :
    networkCompleteObserve a s Omega n x q=networkDataCompleteObserve a s Omega n x.data q := by
  induction q generalizing x with
  | original q => rfl
  | domain op =>
    have square := congrArg Option.isSome (network_operation_actual_data_square a s Omega n op x)
    simpa [networkCompleteObserve,networkDataCompleteObserve,srCompleteOriginalContextObserve] using square
  | after op q ih =>
    change (networkOperation a s Omega n op x).map (fun y => networkCompleteObserve a s Omega n y q)=
      (networkDataOperation a s Omega n op x.data).map (fun d => networkDataCompleteObserve a s Omega n d q)
    rw [←network_operation_actual_data_square a s Omega n op x,Option.map_map]
    congr 1
    funext y
    exact ih y

theorem network_actual_raw_old_profile_square (x : NetworkSource a s Omega n) (i : Fin (n+1)) (q : JointContext) :
    networkCompleteObserve a s Omega n x (.original (.old i q))=
      jointCompleteObserve a s Omega (networkRawJoint a s Omega n x i) q :=
  (congrFun (joint_clock_rebase_complete_context_profile a s Omega (observerSlope x.data.frame*x.epoch i) (networkBaseJoint a s Omega n x.data i)) q).symm

def networkToOldPhysical (i : Fin (n+1)) : NetworkReceiver a s Omega n → JointReceiver a s Omega :=
  ContextualQuotient.descend (networkCompleteObserve a s Omega n)
    (fun x => presentJointOriginal a s Omega (networkRawJoint a s Omega n x i)) (by
      intro x y same
      apply (ContextualQuotient.classify_eq_iff (jointCompleteObserve a s Omega) _ _).mpr
      intro q
      rw [←network_actual_raw_old_profile_square a s Omega n x i q,
        ←network_actual_raw_old_profile_square a s Omega n y i q]
      exact same (.original (.old i q)))

theorem network_old_physical_square (x : NetworkSource a s Omega n) (i : Fin (n+1)) :
    networkToOldPhysical a s Omega n i (presentNetwork a s Omega n x)=
      presentJointOriginal a s Omega (networkRawJoint a s Omega n x i) := rfl

theorem network_all_registered_operations_have_exact_descent (op : NetworkOperation n) :
    ∃! reduced : NetworkReceiver a s Omega n → Option (NetworkReceiver a s Omega n),
      ∀ x, reduced (presentNetwork a s Omega n x)=
        (networkOperation a s Omega n op x).map (presentNetwork a s Omega n) :=
  sr_registered_partial_operation_has_unique_exact_context_descent
    (networkOriginalObserve a s Omega n) (networkOperation a s Omega n) op

theorem network_failed_radar_attempt_is_retained (x : NetworkSource a s Omega n) (index : ℕ) (correction : ℝ)
    (failed : ¬ requestDomain a s Omega n x.data index correction) :
    networkCompleteObserve a s Omega n x (.domain (.certifyRadar index correction))=false ∧
    networkCompleteObserve a s Omega n x (.after (.certifyRadar index correction) (.original .referenceSelection))=none := by
  simp [networkCompleteObserve,srCompleteOriginalContextObserve,networkOperation,networkDataOperation,failed]

end AASCKleinGordon.OperationalSR
