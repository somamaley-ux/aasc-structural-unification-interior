import KGFiniteParticleCore

/-! Actual total spatial momentum multiplication on every finite-particle
symmetric Schwartz sector, then its direct-sum action. This constructs a
common-core operator and its zero vacuum baseline. It does not yet identify
that operator with a hypersurface integral of the attached total EMT. -/
noncomputable section
open scoped SchwartzMap DirectSum
namespace AASCKleinGordon

def totalMomentumCLM (n : ℕ) (j : Fin 3) : ParticleConfiguration n →L[ℝ] ℝ :=
  ∑ i : Fin n, (ContinuousLinearMap.proj j : Momentum →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj i : ParticleConfiguration n →L[ℝ] Momentum)

theorem totalMomentumCLM_apply (n : ℕ) (j : Fin 3) (x : ParticleConfiguration n) :
    totalMomentumCLM n j x=∑ i : Fin n,x i j := by
  simp [totalMomentumCLM]

theorem totalMomentum_permutation (n : ℕ) (j : Fin 3)
    (σ : Equiv.Perm (Fin n)) (x : ParticleConfiguration n) :
    totalMomentumCLM n j (fun i => x (σ i))=totalMomentumCLM n j x := by
  simp only [totalMomentumCLM_apply]
  exact Equiv.sum_comp σ (fun i => x i j)

def totalMomentumComplex (n : ℕ) (j : Fin 3) : ParticleConfiguration n →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (totalMomentumCLM n j)

theorem totalMomentumComplex_temperate (n : ℕ) (j : Fin 3) :
    (fun x => totalMomentumComplex n j x).HasTemperateGrowth :=
  (totalMomentumComplex n j).hasTemperateGrowth

def schwartzTotalMomentum (n : ℕ) (j : Fin 3) :
    𝓢(ParticleConfiguration n,ℂ) →L[ℂ] 𝓢(ParticleConfiguration n,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (totalMomentumComplex n j)

theorem schwartzTotalMomentum_apply (n : ℕ) (j : Fin 3)
    (f : 𝓢(ParticleConfiguration n,ℂ)) (x : ParticleConfiguration n) :
    schwartzTotalMomentum n j f x=(totalMomentumCLM n j x : ℂ)*f x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (totalMomentumComplex_temperate n j) f x

theorem schwartzTotalMomentum_preserves_bosonic (n : ℕ) (j : Fin 3)
    (f : bosonicSchwartz n) : schwartzTotalMomentum n j f.val ∈ bosonicSchwartz n := by
  intro σ x
  rw [schwartzTotalMomentum_apply,schwartzTotalMomentum_apply,totalMomentum_permutation,f.property]

def sectorSpatialMomentum (n : ℕ) (j : Fin 3) : bosonicSchwartz n →ₗ[ℂ] bosonicSchwartz n where
  toFun f := ⟨schwartzTotalMomentum n j f.val,schwartzTotalMomentum_preserves_bosonic n j f⟩
  map_add' f g := by apply Subtype.ext; exact (schwartzTotalMomentum n j).map_add f.val g.val
  map_smul' c f := by apply Subtype.ext; exact (schwartzTotalMomentum n j).map_smul c f.val

def coreSpatialMomentum (j : Fin 3) : FiniteParticleCore →ₗ[ℂ] FiniteParticleCore :=
  DirectSum.lmap (fun n => sectorSpatialMomentum n j)

theorem coreSpatialMomentum_on_sector (j : Fin 3) (n : ℕ) (f : bosonicSchwartz n) :
    coreSpatialMomentum j (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n f)=
      DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n (sectorSpatialMomentum n j f) := by
  exact DirectSum.lmap_lof _ _ _

theorem coreSpatialMomentum_vacuum_zero (j : Fin 3) : coreSpatialMomentum j vacuumCore=0 := by
  rw [vacuumCore,coreSpatialMomentum_on_sector]
  have hz : sectorSpatialMomentum 0 j vacuumSector=0 := by
    apply Subtype.ext
    ext x
    change schwartzTotalMomentum 0 j vacuumSector.val x=0
    rw [schwartzTotalMomentum_apply,totalMomentumCLM_apply]
    simp
  rw [hz,map_zero]

theorem core_spatial_momenta_commute (i j : Fin 3) :
    (coreSpatialMomentum i).comp (coreSpatialMomentum j)=
      (coreSpatialMomentum j).comp (coreSpatialMomentum i) := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro f
  simp only [LinearMap.comp_apply,coreSpatialMomentum_on_sector]
  apply congrArg (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n)
  apply Subtype.ext
  ext x
  change schwartzTotalMomentum n i (schwartzTotalMomentum n j f.val) x=
    schwartzTotalMomentum n j (schwartzTotalMomentum n i f.val) x
  simp only [schwartzTotalMomentum_apply]
  ring

end AASCKleinGordon
