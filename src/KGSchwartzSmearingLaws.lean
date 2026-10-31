import KGBosonicContractionIdentities
import KGCoreFieldOperations

noncomputable section
open MeasureTheory
open scoped SchwartzMap DirectSum
namespace AASCKleinGordon

theorem creationSector_add_smear (n : ℕ) (f g : 𝓢(Momentum,ℂ)) (H : bosonicSchwartz n) :
    creationSectorCLM n (f+g) H = creationSectorCLM n f H + creationSectorCLM n g H := by
  apply Subtype.ext
  have ht : particleTensorInsertCLM n (f+g) H.val =
      particleTensorInsertCLM n f H.val + particleTensorInsertCLM n g H.val := by
    ext y
    simp only [particleTensorInsertCLM_apply, SchwartzMap.add_apply]
    ring
  simp only [creationSectorCLM_apply, ht, map_add, smul_add, Submodule.coe_add]

theorem creationSector_smul_smear (n : ℕ) (c : ℂ) (f : 𝓢(Momentum,ℂ)) (H : bosonicSchwartz n) :
    creationSectorCLM n (c • f) H = c • creationSectorCLM n f H := by
  apply Subtype.ext
  have ht : particleTensorInsertCLM n (c • f) H.val = c • particleTensorInsertCLM n f H.val := by
    ext y
    simp only [particleTensorInsertCLM_apply, SchwartzMap.smul_apply, smul_eq_mul]
    ring
  simp only [creationSectorCLM_apply, ht, map_smul, Submodule.coe_smul]
  exact smul_comm _ _ _

theorem annihilationSector_add_smear (a : Parameters) (n : ℕ) (f g : 𝓢(Momentum,ℂ))
    (H : bosonicSchwartz (n+1)) :
    annihilationSectorCLM a n (f+g) H = annihilationSectorCLM a n f H + annihilationSectorCLM a n g H := by
  apply Subtype.ext
  ext y
  simp only [annihilationSectorCLM_apply, SchwartzMap.add_apply, star_add, add_mul,
    Submodule.coe_add, SchwartzMap.add_apply]
  rw [integral_add (contraction_kernel_integrable a n f H.val y)
    (contraction_kernel_integrable a n g H.val y)]
  ring

theorem annihilationSector_smul_smear (a : Parameters) (n : ℕ) (c : ℂ)
    (f : 𝓢(Momentum,ℂ)) (H : bosonicSchwartz (n+1)) :
    annihilationSectorCLM a n (c • f) H = star c • annihilationSectorCLM a n f H := by
  apply Subtype.ext
  ext y
  simp only [annihilationSectorCLM_apply, SchwartzMap.smul_apply, smul_eq_mul, star_mul,
    Submodule.coe_smul]
  simp_rw [mul_assoc]
  simp_rw [mul_left_comm (star (f _)) (star c)]
  rw [integral_const_mul]
  ring

theorem creationCore_add_smear (f g : 𝓢(Momentum,ℂ)) :
    creationCore (f+g) = creationCore f + creationCore g := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro H
  simp only [LinearMap.comp_apply, creationCore_lof, LinearMap.add_apply, creationSector_add_smear, map_add]

theorem creationCore_smul_smear (c : ℂ) (f : 𝓢(Momentum,ℂ)) :
    creationCore (c • f) = c • creationCore f := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro H
  simp only [LinearMap.comp_apply, creationCore_lof, LinearMap.smul_apply, creationSector_smul_smear, map_smul]

theorem annihilationCore_add_smear (a : Parameters) (f g : 𝓢(Momentum,ℂ)) :
    annihilationCore a (f+g) = annihilationCore a f + annihilationCore a g := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro H
  cases n with
  | zero => simp only [LinearMap.comp_apply, annihilationCore_lof_zero, LinearMap.add_apply, add_zero]
  | succ n => simp only [LinearMap.comp_apply, annihilationCore_lof_succ, LinearMap.add_apply,
      annihilationSector_add_smear, map_add]

theorem annihilationCore_smul_smear (a : Parameters) (c : ℂ) (f : 𝓢(Momentum,ℂ)) :
    annihilationCore a (c • f) = star c • annihilationCore a f := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro H
  cases n with
  | zero => simp only [LinearMap.comp_apply, annihilationCore_lof_zero, LinearMap.smul_apply, smul_zero]
  | succ n => simp only [LinearMap.comp_apply, annihilationCore_lof_succ, LinearMap.smul_apply,
      annihilationSector_smul_smear, map_smul]

end AASCKleinGordon
