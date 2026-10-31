import KGCoherentTensorPowers
import Mathlib.Analysis.SpecialFunctions.Exponential

noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory
open scoped SchwartzMap ENNReal
namespace AASCKleinGordon

def coherentSector (a : Parameters) (f : 𝓢(Momentum,ℂ)) (n : ℕ) : bosonicHilbertSector a n :=
  ((Real.sqrt (n.factorial : ℝ) : ℂ)⁻¹) • bosonicTensorPowerHilbert a f n

theorem coherentSector_norm_sq (a : Parameters) (f : 𝓢(Momentum,ℂ)) (n : ℕ) :
    ‖coherentSector a f n‖^2=(‖oneParticleSchwartzToHilbert a f‖^2)^n/(n.factorial : ℝ) := by
  rw [coherentSector,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,inv_pow,Real.sq_sqrt (Nat.cast_nonneg _),
    bosonicTensorPowerHilbert_norm_sq,← pow_mul]
  ring

theorem coherentSector_memLp (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    Memℓp (coherentSector a f) 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,coherentSector_norm_sq]
  exact (NormedSpace.expSeries_div_hasSum_exp (‖oneParticleSchwartzToHilbert a f‖^2)).summable

/-- The actual exponential vector in the original countable bosonic L2 Fock space. -/
def exponentialVector (a : Parameters) (f : 𝓢(Momentum,ℂ)) : FockHilbert a :=
  ⟨coherentSector a f,coherentSector_memLp a f⟩

@[simp] theorem exponentialVector_component (a : Parameters) (f : 𝓢(Momentum,ℂ)) (n : ℕ) :
    exponentialVector a f n=coherentSector a f n := rfl

theorem coherentSector_inner (a : Parameters) (f g : 𝓢(Momentum,ℂ)) (n : ℕ) :
    inner ℂ (coherentSector a f n) (coherentSector a g n)=
      (inner ℂ (oneParticleSchwartzToHilbert a f) (oneParticleSchwartzToHilbert a g))^n /
        (n.factorial : ℂ) := by
  have hc : (starRingEnd ℂ) ((Real.sqrt (n.factorial : ℝ) : ℂ)⁻¹)*
      (Real.sqrt (n.factorial : ℝ) : ℂ)⁻¹=(n.factorial : ℂ)⁻¹ := by
    simp only [map_inv₀,Complex.conj_ofReal,← mul_inv,← pow_two]
    rw [inv_pow,← Complex.ofReal_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
    simp only [Complex.ofReal_inv,Complex.ofReal_natCast]
  rw [coherentSector,coherentSector,inner_smul_left,inner_smul_right,
    bosonicTensorPowerHilbert_inner,← mul_assoc,hc]
  ring

theorem exponentialVector_inner (a : Parameters) (f g : 𝓢(Momentum,ℂ)) :
    inner ℂ (exponentialVector a f) (exponentialVector a g)=
      Complex.exp (inner ℂ (oneParticleSchwartzToHilbert a f) (oneParticleSchwartzToHilbert a g)) := by
  rw [lp.inner_eq_tsum]
  simp_rw [exponentialVector_component,coherentSector_inner]
  have h:=NormedSpace.expSeries_div_hasSum_exp
    (inner ℂ (oneParticleSchwartzToHilbert a f) (oneParticleSchwartzToHilbert a g))
  rw [← Complex.exp_eq_exp_ℂ] at h
  exact h.tsum_eq

theorem exponentialVector_norm_sq (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    ‖exponentialVector a f‖^2=Real.exp (‖oneParticleSchwartzToHilbert a f‖^2) := by
  have h:=exponentialVector_inner a f f
  rw [inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K] at h
  have he : (‖exponentialVector a f‖^2 : ℂ)=
      (Real.exp (‖oneParticleSchwartzToHilbert a f‖^2) : ℂ) := by
    simpa only [Complex.ofReal_pow,Complex.ofReal_exp] using h
  exact_mod_cast he

theorem exponentialVector_ne_zero (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    exponentialVector a f≠0 := by
  intro hz
  have h:=exponentialVector_norm_sq a f
  rw [hz,norm_zero,zero_pow (by norm_num : (2 : ℕ)≠0)] at h
  exact (Real.exp_pos _).ne' h.symm

theorem exponentialVector_zero (a : Parameters) : exponentialVector a 0=fockVacuum a := by
  rw [fockVacuum,vacuumCore,finiteParticleCoreToFock_on_sector]
  apply lp.ext
  funext n
  cases n with
  | zero =>
    change ((Real.sqrt ((0 : ℕ).factorial : ℝ) : ℂ)⁻¹) •
      bosonicCoreToSector a 0 vacuumSector=
        lp.single (E:=fun n => bosonicHilbertSector a n) 2 0 (bosonicCoreToSector a 0 vacuumSector) 0
    simp
  | succ n =>
    change coherentSector a 0 (n+1)=
      lp.single (E:=fun n => bosonicHilbertSector a n) 2 0 (bosonicCoreToSector a 0 vacuumSector) (n+1)
    simp [coherentSector,bosonicTensorPowerHilbert_zero_succ,lp.single_apply]

end AASCKleinGordon
