import KGCoherentCreationTangent
import KGCoherentOriginalSectors
import KGProductInsertionBridge
import KGDiagonalProductDerivative

noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem sum_mixedTensorPowerSchwartz (n : ℕ) (f g : 𝓢(Momentum,ℂ)) :
    ∑ i : Fin (n+1),mixedTensorPowerSchwartz n i f g=
      (Real.sqrt (n+1) : ℂ) • (creationSectorCLM n g (bosonicTensorPower f n)).val := by
  ext x
  simp only [SchwartzMap.sum_apply,mixedTensorPowerSchwartz_apply,
    SchwartzMap.smul_apply,smul_eq_mul,creationSectorCLM_apply]
  change (∑ i : Fin (n+1),g (x i)*∏ j : Fin n,f (swapDelete n i x j))=
    (Real.sqrt (n+1) : ℂ)*((Real.sqrt (n+1) : ℂ)*
      schwartzSymmetrizer (n+1) (particleTensorInsertCLM n g (schwartzTensorPower f n)) x)
  have hs : schwartzSymmetrizer (n+1) (particleTensorInsertCLM n g (schwartzTensorPower f n)) x=
      ((n+1 : ℕ) : ℂ)⁻¹*(∑ i : Fin (n+1),g (x i)*∏ j : Fin n,f (swapDelete n i x j)) := by
    simpa only [bosonicTensorPower,schwartzTensorPower_apply] using
      symmetrizer_insert_apply n g (bosonicTensorPower f n) x
  rw [hs]
  change _=(Real.sqrt (n+1) : ℂ)*((Real.sqrt (n+1) : ℂ)*
    (((n+1 : ℕ) : ℂ)⁻¹*(∑ i : Fin (n+1),g (x i)*∏ j : Fin n,f (swapDelete n i x j))))
  symm
  calc
    _=((Real.sqrt (n+1) : ℂ)*(Real.sqrt (n+1) : ℂ)*((n+1 : ℕ) : ℂ)⁻¹)*
      (∑ i : Fin (n+1),g (x i)*∏ j : Fin n,f (swapDelete n i x j)) := by ring
    _=_ := by rw [sqrt_particle_factor_cancel,one_mul]

theorem coherentCreationTangent_component_formula (a : Parameters) (g f : 𝓢(Momentum,ℂ)) (n : ℕ) :
    (coherentCreationTangent a g f n).val=coherentFactor n •
      (∑ i : Fin n,particleL2Product a n
        (Function.update (fun _ => oneParticleSchwartzToHilbert a f) i (oneParticleSchwartzToHilbert a g))) := by
  classical
  have hc:=(((bosonicHilbertSector a n).subtypeL.comp (fockSectorEvaluationCLM a n)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (exponentialVector_shift_hasDerivAt_zero a g f)
  change HasDerivAt (fun t : ℝ => (coherentSector a (f+(t : ℂ) • g) n).val)
    (coherentCreationTangent a g f n).val 0 at hc
  have he (t : ℝ) : (coherentSector a (f+(t : ℂ) • g) n).val=
      coherentFactor n • particleL2Product a n
        (fun _ => oneParticleSchwartzToHilbert a (f+(t : ℂ) • g)) := by
    rw [particleL2Product_schwartz_diagonal]
    rfl
  simp_rw [he] at hc
  have hp:=(particleL2Product_diagonal_hasDerivAt a f g n).const_smul (coherentFactor n)
  exact hc.unique hp

theorem coherentCreationTangent_zero_component (a : Parameters) (g f : 𝓢(Momentum,ℂ)) :
    coherentCreationTangent a g f 0=0 := by
  apply Subtype.ext
  simp only [coherentCreationTangent_component_formula,Finset.univ_eq_empty,
    Finset.sum_empty,smul_zero,Submodule.coe_zero]

theorem coherentCreationTangent_succ_component (a : Parameters) (g f : 𝓢(Momentum,ℂ)) (n : ℕ) :
    coherentCreationTangent a g f (n+1)=
      bosonicCoreToSector a (n+1) (creationSectorCLM n g (coherentSectorCore f n)) := by
  classical
  apply Subtype.ext
  rw [coherentCreationTangent_component_formula]
  simp_rw [particleL2Product_update_schwartz]
  rw [← map_sum,sum_mixedTensorPowerSchwartz,map_smul]
  change coherentFactor (n+1) • ((Real.sqrt (n+1 : ℝ) : ℂ) •
      particleSchwartzToHilbert a (n+1) (creationSectorCLM n g (bosonicTensorPower f n)).val)=_
  rw [smul_smul,mul_comm,coherentFactor_succ]
  change _=particleSchwartzToHilbert a (n+1)
    (creationSectorCLM n g (coherentFactor n • bosonicTensorPower f n)).val
  rw [map_smul]
  rfl

end AASCKleinGordon
