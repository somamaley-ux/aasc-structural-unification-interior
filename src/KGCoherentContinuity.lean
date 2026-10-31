import KGCoherentVectors

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap Topology
namespace AASCKleinGordon

theorem exponentialVector_continuous (a : Parameters) : Continuous (exponentialVector a) := by
  apply continuous_iff_continuousAt.mpr
  intro f
  have hs : Continuous (fun g : 𝓢(Momentum,ℂ) => ‖exponentialVector a g-exponentialVector a f‖^2) := by
    simp_rw [norm_sub_sq (𝕜:=ℂ),exponentialVector_norm_sq,exponentialVector_inner]
    exact ((Real.continuous_exp.comp ((oneParticleSchwartzToHilbert a).continuous.norm.pow 2)).sub
      (continuous_const.mul (Complex.continuous_re.comp
        (Complex.continuous_exp.comp ((oneParticleSchwartzToHilbert a).continuous.inner continuous_const))))).add
      continuous_const
  have hn : Continuous (fun g : 𝓢(Momentum,ℂ) => ‖exponentialVector a g-exponentialVector a f‖) := by
    have h : Continuous (fun g : 𝓢(Momentum,ℂ) => Real.sqrt
      (‖exponentialVector a g-exponentialVector a f‖^2)):=Real.continuous_sqrt.comp hs
    simpa only [Real.sqrt_sq_eq_abs,abs_norm] using h
  rw [ContinuousAt,← tendsto_sub_nhds_zero_iff]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [sub_self,norm_zero] using hn.tendsto f

def normalizedCoherentVector (a : Parameters) (f : 𝓢(Momentum,ℂ)) : FockHilbert a :=
  (Real.exp (-‖oneParticleSchwartzToHilbert a f‖^2/2) : ℂ) • exponentialVector a f

theorem normalizedCoherentVector_norm (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    ‖normalizedCoherentVector a f‖=1 := by
  have hs : ‖normalizedCoherentVector a f‖^2=1 := by
    rw [normalizedCoherentVector,norm_smul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _),mul_pow,exponentialVector_norm_sq,pow_two,
      ← Real.exp_add,← Real.exp_add]
    have he : -‖oneParticleSchwartzToHilbert a f‖^2/2+
      -‖oneParticleSchwartzToHilbert a f‖^2/2+‖oneParticleSchwartzToHilbert a f‖^2=0 := by ring
    rw [he,Real.exp_zero]
  nlinarith [norm_nonneg (normalizedCoherentVector a f)]

theorem normalizedCoherentVector_continuous (a : Parameters) :
    Continuous (normalizedCoherentVector a) := by
  exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    (((oneParticleSchwartzToHilbert a).continuous.norm.pow 2).neg.div_const 2))).smul
    (exponentialVector_continuous a)

theorem normalizedCoherentVector_zero (a : Parameters) : normalizedCoherentVector a 0=fockVacuum a := by
  simp [normalizedCoherentVector,exponentialVector_zero]

end AASCKleinGordon
