import KGJointSpectralProjections

noncomputable section
set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
open scoped Topology
namespace AASCKleinGordon

theorem jointSpectralProjection_congr (a : Parameters) (B C : Set FourMomentum)
    (hB : MeasurableSet B) (hC : MeasurableSet C) (h : B=C) :
    jointSpectralProjection a B hB=jointSpectralProjection a C hC := by
  subst C
  rfl

theorem jointSpectralProjection_iUnion_finset (a : Parameters) (B : ℕ → Set FourMomentum)
    (hB : ∀ i,MeasurableSet (B i)) (hd : Pairwise (fun i j => Disjoint (B i) (B j))) (s : Finset ℕ) :
    jointSpectralProjection a (⋃i∈s,B i)
      (MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (fun _ : i∈s => hB i)))=
        ∑i∈s,jointSpectralProjection a (B i) (hB i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using jointSpectralProjection_empty a
  | @insert i s hi ih =>
    have hs : (⋃j∈insert i s,B j)=B i∪⋃j∈s,B j := by ext q; simp
    have hdis : Disjoint (B i) (⋃j∈s,B j) := by
      apply Set.disjoint_left.mpr
      intro q hqi hqs
      obtain ⟨j,hj⟩:=Set.mem_iUnion.mp hqs
      obtain ⟨hjs,hqj⟩:=Set.mem_iUnion.mp hj
      exact Set.disjoint_left.mp (hd (by intro he; subst j; exact hi hjs)) hqi hqj
    calc
      _ = jointSpectralProjection a (B i∪⋃j∈s,B j)
          ((hB i).union (MeasurableSet.iUnion (fun j => MeasurableSet.iUnion (fun _ : j∈s => hB j)))) :=
        jointSpectralProjection_congr a _ _ _ _ hs
      _ = jointSpectralProjection a (B i) (hB i)+jointSpectralProjection a (⋃j∈s,B j)
          (MeasurableSet.iUnion (fun j => MeasurableSet.iUnion (fun _ : j∈s => hB j))) :=
        jointSpectralProjection_union a _ _ _ _ hdis
      _ = _ := by rw [ih,Finset.sum_insert hi]

theorem jointSpectralProjection_iUnion_tendsto (a : Parameters) (B : ℕ → Set FourMomentum)
    (hB : ∀ i,MeasurableSet (B i)) (f : FockHilbert a) :
    Tendsto (fun s : Finset ℕ => jointSpectralProjection a (⋃i∈s,B i)
      (MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (fun _ : i∈s => hB i))) f) atTop
        (𝓝 (jointSpectralProjection a (⋃i,B i) (MeasurableSet.iUnion hB) f)) := by
  apply symbolOperator_tendsto
  intro n
  exact Eventually.of_forall (fun x => by
    classical
    let q:=particleFourMomentum a n x
    change Tendsto (fun s : Finset ℕ => (⋃i∈s,B i).indicator (fun _ => (1 : ℂ)) q) atTop
      (𝓝 ((⋃i,B i).indicator (fun _ => (1 : ℂ)) q))
    have he : ∀ᶠ s : Finset ℕ in atTop,
        (⋃i∈s,B i).indicator (fun _ => (1 : ℂ)) q=(⋃i,B i).indicator (fun _ => (1 : ℂ)) q := by
      by_cases hq:q∈⋃i,B i
      · obtain ⟨i,hi⟩:=Set.mem_iUnion.mp hq
        apply eventually_atTop.mpr
        refine ⟨{i},fun s hs => ?_⟩
        have hm:q∈⋃j∈s,B j:=Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hs (by simp),hi⟩⟩
        simp only [Set.indicator_of_mem hm,Set.indicator_of_mem hq]
      · exact Eventually.of_forall (fun s => by
          have hm:q∉⋃i∈s,B i := by
            intro hh
            obtain ⟨i,hi⟩:=Set.mem_iUnion.mp hh
            obtain ⟨_,hqi⟩:=Set.mem_iUnion.mp hi
            exact hq (Set.mem_iUnion.mpr ⟨i,hqi⟩)
          simp only [Set.indicator_of_notMem hm,Set.indicator_of_notMem hq])
    exact (tendsto_congr' he).mpr tendsto_const_nhds)

theorem jointSpectralProjection_countable_add (a : Parameters) (B : ℕ → Set FourMomentum)
    (hB : ∀ i,MeasurableSet (B i)) (hd : Pairwise (fun i j => Disjoint (B i) (B j))) (f : FockHilbert a) :
    HasSum (fun i => jointSpectralProjection a (B i) (hB i) f)
      (jointSpectralProjection a (⋃i,B i) (MeasurableSet.iUnion hB) f) := by
  have hh:=jointSpectralProjection_iUnion_tendsto a B hB f
  have he : (fun s : Finset ℕ => jointSpectralProjection a (⋃i∈s,B i)
      (MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (fun _ : i∈s => hB i))) f)=
        (fun s : Finset ℕ => ∑i∈s,jointSpectralProjection a (B i) (hB i) f) := by
    funext s
    rw [jointSpectralProjection_iUnion_finset a B hB hd s]
    simp only [ContinuousLinearMap.sum_apply]
  rw [he] at hh
  exact hh

end AASCKleinGordon
