import OSRFiniteNetworkCoverage

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
open Set AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing AASCKleinGordon.CanonicalLicensing.SRIntegration
open scoped BigOperators
namespace AASCKleinGordon.OperationalSR
open KGQuantum W9 TopologicalSpace AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
variable (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint) (n : ℕ)

/- The undirected component is generated only by registered successful reads.
Symmetry reverses the measured offset algebraically; it supplies no new run. -/
inductive ActualRadarConnected (d : NetworkData a s Omega n) : Fin (n+1) → Fin (n+1) → Prop
  | refl (i : Fin (n+1)) : ActualRadarConnected d i i
  | edge (index : ℕ) (correction : ℝ) (r : ExchangeRequest n) (answer : RadarAnswer)
      (registered : d.schedule[index]?=some r)
      (read : radarRead a s Omega n d index correction=some answer) :
      ActualRadarConnected d r.fromSite r.toSite
  | symm {i j : Fin (n+1)} : ActualRadarConnected d i j → ActualRadarConnected d j i
  | trans {i j k : Fin (n+1)} : ActualRadarConnected d i j → ActualRadarConnected d j k → ActualRadarConnected d i k

theorem actual_occupied_path_is_connected (d : NetworkData a s Omega n)
    {i j : Fin (n+1)} (path : OccupiedRadarPath a s Omega n d i j) :
    ActualRadarConnected a s Omega n d i j := by
  induction path with
  | refl i => exact .refl i
  | step index correction r answer registered read tail ih =>
    exact .trans (.edge index correction r answer registered read) ih

theorem actual_undirected_component_synchronization_unique (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (other : Fin (n+1) → ℝ)
    (reads : ∀ index correction r answer, d.schedule[index]?=some r →
      radarRead a s Omega n d index correction=some answer → answer.offset=other r.toSite-other r.fromSite)
    {i j : Fin (n+1)} (connected : ActualRadarConnected a s Omega n d i j) :
    other j-d.sites.phase j=other i-d.sites.phase i := by
  induction connected with
  | refl i => rfl
  | edge index correction r answer registered read =>
    obtain ⟨q,hq,_,offset,_⟩ := every_successful_radar_answer_is_actual a s Omega n d sound index correction answer read
    have same : q=r := Option.some.inj (hq.symm.trans registered)
    subst q
    have alternate := reads index correction r answer registered read
    linarith
  | symm connected ih => exact ih.symm
  | trans left right ihLeft ihRight => exact ihRight.trans ihLeft

theorem actual_undirected_component_has_one_common_origin (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (other : Fin (n+1) → ℝ)
    (reads : ∀ index correction r answer, d.schedule[index]?=some r →
      radarRead a s Omega n d index correction=some answer → answer.offset=other r.toSite-other r.fromSite)
    (base : Fin (n+1)) :
    ∃ origin : ℝ, ∀ j, ActualRadarConnected a s Omega n d base j → other j=d.sites.phase j+origin := by
  refine ⟨other base-d.sites.phase base,?_⟩
  intro j connected
  have same := actual_undirected_component_synchronization_unique a s Omega n d sound other reads connected
  linarith

end AASCKleinGordon.OperationalSR
