import KGL2BosonicPolarization

noncomputable section
set_option maxHeartbeats 2800000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

theorem particleL2Product_schwartz_ae (a : Parameters) (n : ℕ)
    (f : Fin n → 𝓢(Momentum,ℂ)) :
    (particleL2Product a n (fun i => oneParticleSchwartzToHilbert a (f i)) : ParticleConfiguration n → ℂ)
      =ᵐ[particleMeasure a n] (fun x => ∏ i,f i (x i)) := by
  have hf:=Measure.ae_eq_pi (μ:=fun _ : Fin n => wignerMeasure a)
    (fun i => (f i).coeFn_toLp 2 (wignerMeasure a))
  filter_upwards [particleL2Product_ae a n (fun i => oneParticleSchwartzToHilbert a (f i)),hf] with x hx hy
  rw [hx]
  unfold particleProductFunction
  exact congrArg (fun v : Fin n → ℂ => ∏ i,v i) hy

def mixedTensorPowerSchwartz (n : ℕ) (i : Fin (n+1)) (f g : 𝓢(Momentum,ℂ)) :
    𝓢(ParticleConfiguration (n+1),ℂ) :=
  schwartzPermutation (n+1) (Equiv.swap 0 i) (particleTensorInsertCLM n g (schwartzTensorPower f n))

theorem mixedTensorPowerSchwartz_apply (n : ℕ) (i : Fin (n+1)) (f g : 𝓢(Momentum,ℂ))
    (x : ParticleConfiguration (n+1)) :
    mixedTensorPowerSchwartz n i f g x=g (x i)*∏ j : Fin n,f (swapDelete n i x j) := by
  simp only [mixedTensorPowerSchwartz,schwartzPermutation_apply,particleTensorInsertCLM_apply,
    Equiv.swap_apply_left,schwartzTensorPower_apply,Fin.tail,swapDelete]

theorem product_update_swap (n : ℕ) (i : Fin (n+1)) (f g : Momentum → ℂ)
    (x : ParticleConfiguration (n+1)) :
    (∏ j : Fin (n+1), (if j=i then g else f) (x j))=
      g (x i)*∏ j : Fin n,f (swapDelete n i x j) := by
  classical
  let e:=Equiv.swap (0 : Fin (n+1)) i
  let F : Fin (n+1) → ℂ:=fun j => (if j=i then g else f) (x j)
  have hp:=Equiv.prod_comp e F
  change (∏ j,F j)=_
  rw [← hp,Fin.prod_univ_succ]
  have h0 : e 0=i := Equiv.swap_apply_left _ _
  rw [h0]
  have hFi : F i=g (x i) := by simp [F]
  rw [hFi]
  change g (x i)*(∏ j : Fin n,F (e j.succ))=_
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  have hj : e j.succ≠i := by
    intro he
    have hz:=e.injective (he.trans h0.symm)
    exact Fin.succ_ne_zero j hz
  simp only [F,if_neg hj,swapDelete,e]

theorem particleL2Product_update_schwartz (a : Parameters) (n : ℕ) (i : Fin (n+1))
    (f g : 𝓢(Momentum,ℂ)) :
    particleL2Product a (n+1) (Function.update (fun _ => oneParticleSchwartzToHilbert a f) i
      (oneParticleSchwartzToHilbert a g))=
      particleSchwartzToHilbert a (n+1) (mixedTensorPowerSchwartz n i f g) := by
  classical
  have he : Function.update (fun _ : Fin (n+1) => oneParticleSchwartzToHilbert a f) i
      (oneParticleSchwartzToHilbert a g)=
      (fun j : Fin (n+1) => oneParticleSchwartzToHilbert a (if j=i then g else f)) := by
    funext j
    by_cases hj : j=i <;> simp [Function.update_apply,hj]
  rw [he]
  apply Lp.ext
  filter_upwards [particleL2Product_schwartz_ae a (n+1) (fun j => if j=i then g else f),
    (mixedTensorPowerSchwartz n i f g).coeFn_toLp 2 (particleMeasure a (n+1))] with x hx hy
  change (particleSchwartzToHilbert a (n+1) (mixedTensorPowerSchwartz n i f g) :
    ParticleConfiguration (n+1) → ℂ) x=mixedTensorPowerSchwartz n i f g x at hy
  rw [hx,hy,mixedTensorPowerSchwartz_apply]
  convert product_update_swap n i (fun p => f p) (fun p => g p) x using 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j=i <;> simp [hj]

end AASCKleinGordon
