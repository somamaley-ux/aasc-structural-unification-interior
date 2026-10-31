import OSRNetworkSource

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR
open KGQuantum W9 TopologicalSpace AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
variable (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint) (n : ℕ)

theorem recorded_delay_radar_derived_from_actual_null_legs (X Y : SRSpace)
    (tm ta td tp delay : ℝ)
    (incoming : ((ta,Y):SREvent)-(tm,X) ∈ srOriginalFutureRayIncrements)
    (outgoing : ((tp,X):SREvent)-(td,Y) ∈ srOriginalFutureRayIncrements)
    (recorded_wait : td-ta=delay) :
    ta=(tm+tp-delay)/2 ∧ td=(tm+tp+delay)/2 ∧
      (tp-tm-delay)/2=‖Y-X‖ := by
  have inward : ‖Y-X‖=ta-tm := incoming.2
  have outward : ‖X-Y‖=tp-td := outgoing.2
  rw [norm_sub_rev X Y] at outward
  constructor
  · linarith
  · constructor <;> linarith

theorem every_successful_radar_answer_is_actual (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (index : ℕ) (correction : ℝ) (answer : RadarAnswer)
    (read : radarRead a s Omega n d index correction=some answer) :
    ∃ r : ExchangeRequest n, d.schedule[index]?=some r ∧
      answer=actualRadarAnswer a s Omega n d index r ∧
      answer.offset=d.sites.phase r.toSite-d.sites.phase r.fromSite ∧
      answer.length=‖d.sites.position r.toSite-d.sites.position r.fromSite‖ := by
  have inside := (radar_read_exact_domain a s Omega n d index correction).mp (by rw [read];rfl)
  have saved := inside
  obtain ⟨r,registered,_⟩ := inside
  rw [radarRead,if_pos saved,registered,Option.map_some,Option.some.injEq] at read
  subst answer
  exact ⟨r,registered,rfl,(occupied_network_radar_answer a s Omega n d sound index r).1,
    (occupied_network_radar_answer a s Omega n d sound index r).2⟩

inductive OccupiedRadarPath (d : NetworkData a s Omega n) : Fin (n+1) → Fin (n+1) → Type
  | refl (i : Fin (n+1)) : OccupiedRadarPath d i i
  | step (index : ℕ) (correction : ℝ) (r : ExchangeRequest n) (answer : RadarAnswer)
      (registered : d.schedule[index]?=some r) (read : radarRead a s Omega n d index correction=some answer)
      {j : Fin (n+1)} (tail : OccupiedRadarPath d r.toSite j) : OccupiedRadarPath d r.fromSite j

def occupiedRadarPathSum {d : NetworkData a s Omega n} {i j : Fin (n+1)} : OccupiedRadarPath a s Omega n d i j → ℝ
  | .refl _ => 0
  | .step _ _ _ answer _ _ tail => answer.offset+occupiedRadarPathSum tail

theorem occupied_radar_path_sum_is_actual_phase_difference {d : NetworkData a s Omega n}
    (sound : networkSound a s Omega n d) {i j : Fin (n+1)} (path : OccupiedRadarPath a s Omega n d i j) :
    occupiedRadarPathSum a s Omega n path=d.sites.phase j-d.sites.phase i := by
  induction path with
  | refl i => simp [occupiedRadarPathSum]
  | step index correction r answer registered read tail ih =>
    obtain ⟨q,hq,_,offset,_⟩ := every_successful_radar_answer_is_actual a s Omega n d sound index correction answer read
    have same : q=r := Option.some.inj (hq.symm.trans registered)
    subst q
    simp only [occupiedRadarPathSum]
    rw [offset,ih]
    ring

theorem every_occupied_radar_loop_sums_to_zero {d : NetworkData a s Omega n}
    (sound : networkSound a s Omega n d) (i : Fin (n+1)) (loop : OccupiedRadarPath a s Omega n d i i) :
    occupiedRadarPathSum a s Omega n loop=0 := by
  rw [occupied_radar_path_sum_is_actual_phase_difference a s Omega n sound loop,sub_self]

theorem measured_ruler_answer_has_actual_simultaneous_events (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (i j : Fin (n+1)) (T : ℝ)
    (domain : rulerDomain a s Omega n d i j T) :
    ∃ X Y : SREvent, rulerRead a s Omega n d i j T=some (X,Y,‖Y.2-X.2‖) ∧ X.1=T ∧ Y.1=T := by
  refine ⟨measuredEndpoint d.frame d.origin T (d.sites.position i),
    measuredEndpoint d.frame d.origin T (d.sites.position j),?_,?_,?_⟩
  · simp [rulerRead,domain]
  · exact (measuring_frame_selected_events_actual_and_unique d.frame sound.2.1 d.origin T _).1
  · exact (measuring_frame_selected_events_actual_and_unique d.frame sound.2.1 d.origin T _).1

end AASCKleinGordon.OperationalSR
