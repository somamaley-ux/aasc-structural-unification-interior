import KGCoherentTensorPowers
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped SchwartzMap
namespace AASCKleinGordon

def particleProductFunction (a : Parameters) (n : ℕ) (f : Fin n → OneParticleHilbert a)
    (x : ParticleConfiguration n) : ℂ := ∏ i,f i (x i)

theorem particleProductFunction_stronglyMeasurable (a : Parameters) (n : ℕ)
    (f : Fin n → OneParticleHilbert a) : StronglyMeasurable (particleProductFunction a n f) :=
  Finset.stronglyMeasurable_fun_prod _ (fun i _ =>
    (Lp.stronglyMeasurable (f i)).comp_measurable (measurable_pi_apply i))

theorem particleProductFunction_memLp (a : Parameters) (n : ℕ)
    (f : Fin n → OneParticleHilbert a) : MemLp (particleProductFunction a n f) 2 (particleMeasure a n) := by
  apply (memLp_two_iff_integrable_sq_norm (particleProductFunction_stronglyMeasurable a n f).aestronglyMeasurable).mpr
  have h:=Integrable.fin_nat_prod (fun i : Fin n =>
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (f i))).mp (Lp.memLp (f i)))
  simpa only [particleProductFunction,norm_prod,Finset.prod_pow,particleMeasure] using h

def particleL2Product (a : Parameters) (n : ℕ) (f : Fin n → OneParticleHilbert a) : ParticleHilbert a n :=
  (particleProductFunction_memLp a n f).toLp (particleProductFunction a n f)

theorem particleL2Product_ae (a : Parameters) (n : ℕ) (f : Fin n → OneParticleHilbert a) :
    (particleL2Product a n f : ParticleConfiguration n → ℂ)=ᵐ[particleMeasure a n]
      particleProductFunction a n f := (particleProductFunction_memLp a n f).coeFn_toLp

theorem particleL2Product_inner (a : Parameters) (n : ℕ) (f g : Fin n → OneParticleHilbert a) :
    inner ℂ (particleL2Product a n f) (particleL2Product a n g)=∏ i,inner ℂ (f i) (g i) := by
  rw [L2.inner_def]
  calc
    _=∫ x, star (particleProductFunction a n f x)*particleProductFunction a n g x ∂particleMeasure a n := by
      apply integral_congr_ae
      filter_upwards [particleL2Product_ae a n f,particleL2Product_ae a n g] with x hx hy
      rw [hx,hy]
      exact RCLike.inner_apply' _ _
    _=∫ x : ParticleConfiguration n, ∏ i, star (f i (x i))*g i (x i) ∂particleMeasure a n := by
      congr 1
      funext x
      simp only [particleProductFunction,star_prod,Finset.prod_mul_distrib]
    _=∏ i,inner ℂ (f i) (g i) := by
      rw [particleMeasure]
      have hfub:=integral_fin_nat_prod_eq_prod (μ:=fun _ : Fin n => wignerMeasure a)
        (fun i x => star (f i x)*g i x)
      rw [hfub]
      apply Finset.prod_congr rfl
      intro i _
      rw [L2.inner_def]
      congr 1
      funext x
      exact (RCLike.inner_apply' _ _).symm

theorem particleL2Product_norm (a : Parameters) (n : ℕ) (f : Fin n → OneParticleHilbert a) :
    ‖particleL2Product a n f‖=∏ i,‖f i‖ := by
  have h:=particleL2Product_inner a n f f
  simp only [inner_self_eq_norm_sq_to_K] at h
  have hs : ‖particleL2Product a n f‖^2=∏ i,‖f i‖^2 := by exact_mod_cast h
  rw [Finset.prod_pow] at hs
  nlinarith [norm_nonneg (particleL2Product a n f),Finset.prod_nonneg (fun i (_ : i∈Finset.univ) => norm_nonneg (f i))]

theorem particleL2Product_schwartz_diagonal (a : Parameters) (f : 𝓢(Momentum,ℂ)) (n : ℕ) :
    particleL2Product a n (fun _ => oneParticleSchwartzToHilbert a f)=
      particleSchwartzToHilbert a n (schwartzTensorPower f n) := by
  apply Lp.ext
  have hf:=Measure.ae_eq_pi (μ:=fun _ : Fin n => wignerMeasure a)
    (fun _ => f.coeFn_toLp 2 (wignerMeasure a))
  filter_upwards [particleL2Product_ae a n (fun _ => oneParticleSchwartzToHilbert a f),hf,
    (schwartzTensorPower f n).coeFn_toLp 2 (particleMeasure a n)] with x hx hy hz
  change (particleSchwartzToHilbert a n (schwartzTensorPower f n) : ParticleConfiguration n → ℂ) x=
    schwartzTensorPower f n x at hz
  rw [hx,hz,schwartzTensorPower_apply]
  unfold particleProductFunction
  exact congrArg (fun v : Fin n → ℂ => ∏ i,v i) hy

end AASCKleinGordon
