import KGJointMomentumCone
import KGFockSymbolConvergence

noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
open scoped Topology
namespace AASCKleinGordon

def jointCutoffSymbol (a : Parameters) (B : Set FourMomentum) (hB : MeasurableSet B) :
    FockContractiveSymbol a where
  value n x:=B.indicator (fun _ => (1 : ℂ)) (particleFourMomentum a n x)
  measurable n:=(measurable_const.indicator hB).comp (particleFourMomentum_continuous a n).measurable
  invariant n σ x:=by rw [particleFourMomentum_permutation]
  bound n x:=by
    classical
    by_cases h:particleFourMomentum a n x∈B <;> simp [h]

def jointSpectralProjection (a : Parameters) (B : Set FourMomentum) (hB : MeasurableSet B) :
    FockHilbert a →L[ℂ] FockHilbert a := symbolOperator a (jointCutoffSymbol a B hB)

theorem jointSpectralProjection_ae (a : Parameters) (B : Set FourMomentum) (hB : MeasurableSet B)
    (f : FockHilbert a) (n : ℕ) :
    (jointSpectralProjection a B hB f n).val=ᵐ[particleMeasure a n]
      (fun x => B.indicator (fun _ => (1 : ℂ)) (particleFourMomentum a n x)*(f n).val x) :=
  symbolOperator_ae a (jointCutoffSymbol a B hB) f n

theorem jointSpectralProjection_univ (a : Parameters) :
    jointSpectralProjection a Set.univ MeasurableSet.univ=ContinuousLinearMap.id ℂ (FockHilbert a) := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext n
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [jointSpectralProjection_ae a Set.univ MeasurableSet.univ f n] with x hx
  simpa using hx

theorem jointSpectralProjection_empty (a : Parameters) :
    jointSpectralProjection a ∅ MeasurableSet.empty=0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext n
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [jointSpectralProjection_ae a ∅ MeasurableSet.empty f n,
    Lp.coeFn_zero ℂ 2 (particleMeasure a n)] with x hx hz
  have hh : (jointSpectralProjection a ∅ MeasurableSet.empty f n).val x=0 := by simpa using hx
  exact hh.trans hz.symm

theorem jointSpectralProjection_inter (a : Parameters) (B C : Set FourMomentum)
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    (jointSpectralProjection a B hB).comp (jointSpectralProjection a C hC)=
      jointSpectralProjection a (B∩C) (hB.inter hC) := by
  rw [jointSpectralProjection,jointSpectralProjection,symbolOperator_product,jointSpectralProjection]
  apply symbolOperator_eq_of_value_eq
  intro n x
  classical
  change B.indicator (fun _ => (1 : ℂ)) (particleFourMomentum a n x)*
    C.indicator (fun _ => (1 : ℂ)) (particleFourMomentum a n x)=
      (B∩C).indicator (fun _ => (1 : ℂ)) (particleFourMomentum a n x)
  by_cases hb:particleFourMomentum a n x∈B <;>
    by_cases hc:particleFourMomentum a n x∈C <;> simp [hb,hc]

theorem jointSpectralProjection_symmetric (a : Parameters) (B : Set FourMomentum)
    (hB : MeasurableSet B) (f g : FockHilbert a) :
    inner ℂ (jointSpectralProjection a B hB f) g=inner ℂ f (jointSpectralProjection a B hB g) := by
  apply symbolOperator_symmetric
  intro n x
  classical
  change star (B.indicator (fun _ => (1 : ℂ)) (particleFourMomentum a n x))=_
  by_cases hb:particleFourMomentum a n x∈B <;> simp [hb,jointCutoffSymbol]

theorem jointSpectralProjection_union (a : Parameters) (B C : Set FourMomentum)
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hd : Disjoint B C) :
    jointSpectralProjection a (B∪C) (hB.union hC)=
      jointSpectralProjection a B hB+jointSpectralProjection a C hC := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext n
  apply Subtype.ext
  apply Lp.ext
  have he (q : FourMomentum) : (B∪C).indicator (fun _ => (1 : ℂ)) q=
      B.indicator (fun _ => (1 : ℂ)) q+C.indicator (fun _ => (1 : ℂ)) q := by
    classical
    by_cases hb:q∈B
    · have hc:q∉C:=fun hc => Set.disjoint_left.mp hd hb hc
      simp [hb,hc]
    · by_cases hc:q∈C <;> simp [hb,hc]
  filter_upwards [jointSpectralProjection_ae a (B∪C) (hB.union hC) f n,
    jointSpectralProjection_ae a B hB f n,jointSpectralProjection_ae a C hC f n,
    Lp.coeFn_add (jointSpectralProjection a B hB f n).val
      (jointSpectralProjection a C hC f n).val] with x hx hy hz hw
  change (jointSpectralProjection a (B∪C) (hB.union hC) f n).val x=
    ((jointSpectralProjection a B hB f n).val+(jointSpectralProjection a C hC f n).val) x
  simp only [Pi.add_apply] at hw
  rw [hx,hw,hy,hz,he,add_mul]

theorem futureMomentumCone_measurable : MeasurableSet futureMomentumCone := by
  apply IsClosed.measurableSet
  apply isClosed_le _ (continuous_apply 0)
  exact (momentumEuclidean.continuous.comp (continuous_pi (fun j => continuous_apply j.succ))).norm

theorem jointSpectralProjection_futureCone (a : Parameters) :
    jointSpectralProjection a futureMomentumCone futureMomentumCone_measurable=
      ContinuousLinearMap.id ℂ (FockHilbert a) := by
  rw [← jointSpectralProjection_univ a]
  apply symbolOperator_eq_of_value_eq
  intro n x
  simp only [jointCutoffSymbol,Set.indicator_of_mem (particleFourMomentum_mem_futureCone a n x),
    Set.indicator_of_mem (Set.mem_univ _)]

end AASCKleinGordon
