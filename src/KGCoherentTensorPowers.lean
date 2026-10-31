import KGGeneralPoincareRepresentation
import KGParticleAdjointness
import KGCoreCCR

noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

/-- Actual original Schwartz tensor powers, before exponential normalization. -/
def schwartzTensorPower (f : 𝓢(Momentum,ℂ)) : (n : ℕ) → 𝓢(ParticleConfiguration n,ℂ)
  | 0 => vacuumSchwartz
  | n+1 => particleTensorInsertCLM n f (schwartzTensorPower f n)

theorem schwartzTensorPower_apply (f : 𝓢(Momentum,ℂ)) (n : ℕ) (x : ParticleConfiguration n) :
    schwartzTensorPower f n x=∏ i, f (x i) := by
  induction n with
  | zero => change (1 : ℂ)=∏ i : Fin 0,f (x i); simp
  | succ n ih =>
    rw [schwartzTensorPower,particleTensorInsertCLM_apply,ih,Fin.prod_univ_succ]
    rfl

theorem schwartzTensorPower_bosonic (f : 𝓢(Momentum,ℂ)) (n : ℕ) :
    schwartzTensorPower f n∈bosonicSchwartz n := by
  intro σ x
  simp only [schwartzTensorPower_apply]
  exact Equiv.prod_comp σ (fun i => f (x i))

def bosonicTensorPower (f : 𝓢(Momentum,ℂ)) (n : ℕ) : bosonicSchwartz n :=
  ⟨schwartzTensorPower f n,schwartzTensorPower_bosonic f n⟩

def bosonicTensorPowerHilbert (a : Parameters) (f : 𝓢(Momentum,ℂ)) (n : ℕ) :
    bosonicHilbertSector a n := bosonicCoreToSector a n (bosonicTensorPower f n)

theorem schwartzTensorPower_inner (a : Parameters) (f g : 𝓢(Momentum,ℂ)) (n : ℕ) :
    inner ℂ (particleSchwartzToHilbert a n (schwartzTensorPower f n))
      (particleSchwartzToHilbert a n (schwartzTensorPower g n))=
      (inner ℂ (oneParticleSchwartzToHilbert a f) (oneParticleSchwartzToHilbert a g))^n := by
  induction n with
  | zero =>
    rw [particle_schwartz_inner_eq]
    change (∫ _ : ParticleConfiguration 0,star (1 : ℂ)*1 ∂particleMeasure a 0)=_ ^ 0
    simp
  | succ n ih =>
    rw [schwartzTensorPower,schwartzTensorPower,particle_tensor_contraction_adjoint,
      particleContraction_tensorInsert,map_smul,inner_smul_right,ih,
      test_pair_integral_eq_inner,pow_succ]
    ring

theorem bosonicTensorPowerHilbert_inner (a : Parameters) (f g : 𝓢(Momentum,ℂ)) (n : ℕ) :
    inner ℂ (bosonicTensorPowerHilbert a f n) (bosonicTensorPowerHilbert a g n)=
      (inner ℂ (oneParticleSchwartzToHilbert a f) (oneParticleSchwartzToHilbert a g))^n :=
  schwartzTensorPower_inner a f g n

theorem bosonicTensorPowerHilbert_norm_sq (a : Parameters) (f : 𝓢(Momentum,ℂ)) (n : ℕ) :
    ‖bosonicTensorPowerHilbert a f n‖^2=‖oneParticleSchwartzToHilbert a f‖^(2*n) := by
  have h:=bosonicTensorPowerHilbert_inner a f f n
  rw [inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K] at h
  have hr : ‖bosonicTensorPowerHilbert a f n‖^2=
      (‖oneParticleSchwartzToHilbert a f‖^2)^n := by exact_mod_cast h
  simpa only [pow_mul] using hr

theorem schwartzTensorPower_smul (z : ℂ) (f : 𝓢(Momentum,ℂ)) (n : ℕ) :
    schwartzTensorPower (z • f) n=z^n • schwartzTensorPower f n := by
  ext x
  simp only [schwartzTensorPower_apply,SchwartzMap.smul_apply,smul_eq_mul]
  rw [Finset.prod_mul_distrib]
  simp

theorem bosonicTensorPowerHilbert_smul (a : Parameters) (z : ℂ) (f : 𝓢(Momentum,ℂ)) (n : ℕ) :
    bosonicTensorPowerHilbert a (z • f) n=z^n • bosonicTensorPowerHilbert a f n := by
  unfold bosonicTensorPowerHilbert
  rw [show bosonicTensorPower (z • f) n=z^n • bosonicTensorPower f n from
    Subtype.ext (schwartzTensorPower_smul z f n),map_smul]

theorem bosonicTensorPowerHilbert_zero_succ (a : Parameters) (n : ℕ) :
    bosonicTensorPowerHilbert a 0 (n+1)=0 := by
  have h : bosonicTensorPower 0 (n+1)=0 := by
    apply Subtype.ext
    ext x
    simp [bosonicTensorPower,schwartzTensorPower,particleTensorInsertCLM_apply]
  rw [bosonicTensorPowerHilbert,h,map_zero]

end AASCKleinGordon
