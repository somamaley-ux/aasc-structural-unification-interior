import OSRPopulatedProtocol

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

def allPairsSchedule : List (ExchangeRequest n) :=
  (Finset.univ : Finset (Fin (n+1) × Fin (n+1))).toList.map (fun p => ⟨p.1,p.2,0,0,1⟩)

theorem all_pairs_request_actually_registered (i j : Fin (n+1)) :
    ∃ index : ℕ, (allPairsSchedule n)[index]?=some (⟨i,j,0,0,1⟩ : ExchangeRequest n) := by
  apply List.mem_iff_getElem?.mp
  apply List.mem_map.mpr
  exact ⟨(i,j),by simp,rfl⟩

theorem finite_all_pairs_network_is_actually_occupied
    (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega})
    (sites : Fin (n+1) → SRSpace) (phase : Fin (n+1) → ℝ) :
    ∃ d : NetworkData a s Omega n, networkSound a s Omega n d ∧ d.sites.position=sites ∧ d.sites.phase=phase ∧
      ∀ i j, sites j ≠ sites i → ∃ index answer,
        d.schedule[index]?=some (⟨i,j,0,0,1⟩ : ExchangeRequest n) ∧
        radarRead a s Omega n d index 0=some answer ∧
        answer.offset=phase j-phase i ∧ answer.length=‖sites j-sites i‖ := by
  let R := ∑ k, ‖sites k‖
  have nonnegative : 0 ≤ R := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have bound : ∀ k, ‖sites k‖ ≤ R := fun k => Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ k)
  let d := populatedNetworkData a s Omega n r H sites phase 0 (4*R+1) (allPairsSchedule n)
  have sound := populated_network_actual_sound a s Omega n r H sites phase 0 (4*R+1) (by linarith) (allPairsSchedule n)
  refine ⟨d,sound,rfl,rfl,?_⟩
  intro i j distinct
  obtain ⟨index,registered⟩ := all_pairs_request_actually_registered n i j
  let request : ExchangeRequest n := ⟨i,j,0,0,1⟩
  have normBound : ‖sites j-sites i‖ ≤ 2*R := by
    have triangle := norm_sub_le (sites j) (sites i)
    linarith [bound i,bound j]
  have domain := populated_network_every_declared_valid_request_is_executed a s Omega n r H sites phase
    0 (4*R+1) (allPairsSchedule n) index request registered distinct (by norm_num [request])
    (by norm_num [request]) (by norm_num [request]) (by dsimp [request];linarith)
  refine ⟨index,actualRadarAnswer a s Omega n d index request,registered,?_,?_,?_⟩
  · rw [radarRead,if_pos domain]
    have lookup : d.schedule[index]?=some request := registered
    rw [lookup]
    rfl
  · exact (occupied_network_radar_answer a s Omega n d sound index request).1
  · exact (occupied_network_radar_answer a s Omega n d sound index request).2

theorem synchronization_from_actual_successful_graph (d : NetworkData a s Omega n)
    (other : Fin (n+1) → ℝ)
    (reads : ∀ index correction r answer, d.schedule[index]?=some r →
      radarRead a s Omega n d index correction=some answer → answer.offset=other r.toSite-other r.fromSite)
    {i j : Fin (n+1)} (path : OccupiedRadarPath a s Omega n d i j) :
    occupiedRadarPathSum a s Omega n path=other j-other i := by
  induction path with
  | refl i => simp [occupiedRadarPathSum]
  | step index correction r answer registered read tail ih =>
    simp only [occupiedRadarPathSum]
    rw [reads index correction r answer registered read,ih]
    ring

theorem actual_component_synchronization_unique (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (other : Fin (n+1) → ℝ)
    (reads : ∀ index correction r answer, d.schedule[index]?=some r →
      radarRead a s Omega n d index correction=some answer → answer.offset=other r.toSite-other r.fromSite)
    {i j : Fin (n+1)} (path : OccupiedRadarPath a s Omega n d i j) :
    other j-d.sites.phase j=other i-d.sites.phase i := by
  have actual := occupied_radar_path_sum_is_actual_phase_difference a s Omega n sound path
  have same := synchronization_from_actual_successful_graph a s Omega n d other reads path
  linarith

theorem actual_radar_reversal_from_successful_records (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (p q : ExchangeRequest n) (i j : ℕ) (correctionP correctionQ : ℝ)
    (answerP answerQ : RadarAnswer) (regP : d.schedule[i]?=some p) (regQ : d.schedule[j]?=some q)
    (readP : radarRead a s Omega n d i correctionP=some answerP)
    (readQ : radarRead a s Omega n d j correctionQ=some answerQ)
    (fromEq : q.fromSite=p.toSite) (toEq : q.toSite=p.fromSite) : answerQ.offset = -answerP.offset := by
  obtain ⟨rp,regp,_,op,_⟩ := every_successful_radar_answer_is_actual a s Omega n d sound i correctionP answerP readP
  obtain ⟨rq,regq,_,oq,_⟩ := every_successful_radar_answer_is_actual a s Omega n d sound j correctionQ answerQ readQ
  have ep : rp=p := Option.some.inj (regp.symm.trans regP)
  have eq : rq=q := Option.some.inj (regq.symm.trans regQ)
  subst rp
  subst rq
  rw [op,oq,fromEq,toEq]
  ring

end AASCKleinGordon.OperationalSR
