import OSROccupiedRelay

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR
attribute [local instance] Classical.propDecidable

def relayCompensatorIncoming (R : RelayData) : SREvent :=
  ((relayTurn R).1-1,relayCompensatorPosition R ((relayTurn R).1-1))
def relayCompensatorOutgoing (R : RelayData) : SREvent :=
  ((relayTurn R).1+1,relayCompensatorPosition R ((relayTurn R).1+1))

def relaySegments (R : RelayData) : List (SREvent × SREvent) :=
  [(relayDeparture R,relayTurn R),(relayTurn R,relayReturn R),
   (relayDeparture R,relayReturn R),(relayArrival R,relayRelease R),
   (relayCompensatorIncoming R,relayTurn R),(relayTurn R,relayCompensatorOutgoing R)]

def relayCovered (O : Set SREvent) (R : RelayData) : Prop :=
  ∀ edge ∈ relaySegments R, segmentCovered O edge.1 edge.2

theorem relay_compensator_full_legs_are_original_rays (R : RelayData) (unit : ‖R.direction‖=1) :
    relayTurn R-relayCompensatorIncoming R ∈ srOriginalFutureRayIncrements ∧
    relayCompensatorOutgoing R-relayTurn R ∈ srOriginalFutureRayIncrements := by
  have incoming : relayTurn R-relayCompensatorIncoming R=(1,-R.direction) := by
    apply Prod.ext
    · simp [relayCompensatorIncoming]
    · simp [relayCompensatorIncoming,relayCompensatorPosition,relayTurn,relayZ]
  have outgoing : relayCompensatorOutgoing R-relayTurn R=(1,R.direction) := by
    apply Prod.ext
    · simp [relayCompensatorOutgoing]
    · have after : ¬ (relayTurn R).1+1 ≤ (relayTurn R).1 := by linarith
      rw [relayCompensatorOutgoing,relayCompensatorPosition,if_neg after]
      simp [relayTurn]
  rw [incoming,outgoing]
  constructor
  · simpa [srNativePositiveRayMomentum] using (sr_native_positive_energy_ray_is_original_future_null 1 (by norm_num) (-R.direction) (by simpa using unit)).1
  · simpa [srNativePositiveRayMomentum] using (sr_native_positive_energy_ray_is_original_future_null 1 (by norm_num) R.direction unit).1

theorem relay_whole_affine_domain_populated (R : RelayData) : relayCovered univ R := by
  intro edge _ t _
  trivial

theorem relay_whole_segments_transport (A : SRMatrixFrame) (b : SREvent) (O : Set SREvent) (R : RelayData) :
    relayCovered O R ↔ ∀ edge ∈ relaySegments R,
      segmentCovered (frameEvent A b '' O) (frameEvent A b edge.1) (frameEvent A b edge.2) := by
  constructor
  · intro covered edge member
    exact (actual_segment_domain_transport A b edge.1 edge.2 O).mpr (covered edge member)
  · intro covered edge member
    exact (actual_segment_domain_transport A b edge.1 edge.2 O).mp (covered edge member)

def protocolTimeSlab (lo hi : ℝ) : Set SREvent := {p | lo < p.1 ∧ p.1 < hi}

theorem protocol_time_slab_open (lo hi : ℝ) : IsOpen (protocolTimeSlab lo hi) :=
  isOpen_Ioo.preimage continuous_fst

theorem time_slab_full_segment (lo hi : ℝ) (p q : SREvent)
    (pin : p ∈ protocolTimeSlab lo hi) (qin : q ∈ protocolTimeSlab lo hi) :
    segmentCovered (protocolTimeSlab lo hi) p q := by
  intro t ht
  change lo < (1-t)*p.1+t*q.1 ∧ (1-t)*p.1+t*q.1 < hi
  constructor
  · have left := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr pin.1.le)
    by_cases zero : t=0
    · simpa [zero] using pin.1
    · have strict := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm zero)) (sub_pos.mpr qin.1)
      nlinarith
  · have left := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr pin.2.le)
    have right := mul_nonneg ht.1 (sub_nonneg.mpr qin.2.le)
    by_cases zero : t=0
    · simp [zero]
      exact pin.2
    · have strict := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm zero)) (sub_pos.mpr qin.2)
      nlinarith

theorem relay_proper_restricted_domain_populated (R : RelayData) (length : 0 < R.length)
    (delay : 0 ≤ R.delay) :
    relayCovered (protocolTimeSlab (R.emit-2) ((relayReturn R).1+2)) R ∧
    protocolTimeSlab (R.emit-2) ((relayReturn R).1+2) ≠ univ := by
  have L : 0 < relayLength R := by dsimp [relayLength];linarith
  constructor
  · intro edge member
    simp only [relaySegments,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      apply time_slab_full_segment <;>
      change R.emit-2 < _ ∧ _ < (relayReturn R).1+2 <;>
      dsimp [relayDeparture,relayTurn,relayReturn,relayArrival,relayRelease,relayCompensatorIncoming,
        relayCompensatorOutgoing,relayLength] at * <;> constructor <;> linarith
  · intro equal
    have member : ((R.emit-2,(0:SRSpace)):SREvent) ∈ protocolTimeSlab (R.emit-2) ((relayReturn R).1+2) := by
      rw [equal]
      trivial
    exact lt_irrefl (R.emit-2) member.1

inductive AdmittedPath {ι : Type} (edge : ι → ι → Prop) : ι → ι → Prop
  | refl (i : ι) : AdmittedPath edge i i
  | step (i j k : ι) : edge i j → AdmittedPath edge j k → AdmittedPath edge i k

theorem synchronization_unique_on_actual_component {ι : Type} (edge : ι → ι → Prop)
    (phase other : ι → ℝ) (same_offsets : ∀ i j, edge i j → other j-other i=phase j-phase i)
    (i j : ι) (path : AdmittedPath edge i j) : other j-phase j=other i-phase i := by
  induction path with
  | refl => rfl
  | step i j k adjacent _ ih =>
    have same := same_offsets i j adjacent
    linarith

theorem all_pairs_synchronization_has_one_origin {n : ℕ} (phase other : Fin (n+1) → ℝ)
    (same_offsets : ∀ i j, other j-other i=phase j-phase i) :
    ∃ origin : ℝ, ∀ i, other i=phase i+origin := by
  refine ⟨other 0-phase 0,?_⟩
  intro i
  have same := same_offsets 0 i
  linarith

end AASCKleinGordon.OperationalSR
