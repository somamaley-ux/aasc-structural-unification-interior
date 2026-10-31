import KGCoreEnergy
import KGSchwartzMomentumCoefficient

noncomputable section
open scoped SchwartzMap
namespace AASCKleinGordon

theorem energyCoefficientB_temperate (a : Parameters) (n : ℕ) :
    (fun x => Multiplication.graphCoefficientB (particleTotalEnergy a n x)).HasTemperateGrowth :=
  graphCoefficientB_temperate.comp (particleTotalEnergy_temperate a n)

def schwartzEnergyCoefficientB (a : Parameters) (n : ℕ) :
    𝓢(ParticleConfiguration n,ℂ) →L[ℂ] 𝓢(ParticleConfiguration n,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x => Multiplication.graphCoefficientB (particleTotalEnergy a n x))

theorem schwartzEnergyCoefficientB_apply (a : Parameters) (n : ℕ)
    (f : 𝓢(ParticleConfiguration n,ℂ)) (x : ParticleConfiguration n) :
    schwartzEnergyCoefficientB a n f x=
      Multiplication.graphCoefficientB (particleTotalEnergy a n x)*f x :=
  SchwartzMap.smulLeftCLM_apply_apply (energyCoefficientB_temperate a n) f x

def bosonicSchwartzEnergyCoefficientB (a : Parameters) (n : ℕ) :
    bosonicSchwartz n →ₗ[ℂ] bosonicSchwartz n where
  toFun f := ⟨schwartzEnergyCoefficientB a n f.val,by
    intro σ x
    rw [schwartzEnergyCoefficientB_apply,schwartzEnergyCoefficientB_apply,
      particleTotalEnergy_permutation,f.property]⟩
  map_add' f g := by apply Subtype.ext; exact (schwartzEnergyCoefficientB a n).map_add f.val g.val
  map_smul' c f := by apply Subtype.ext; exact (schwartzEnergyCoefficientB a n).map_smul c f.val

theorem bosonicEnergyCoefficientB_intertwines (a : Parameters) (n : ℕ) (f : bosonicSchwartz n) :
    Multiplication.graphBoundedB (particleTotalEnergy a n) (particleTotalEnergy_continuous a n).measurable
        (bosonicCoreToSector a n f).val=
      (bosonicCoreToSector a n (bosonicSchwartzEnergyCoefficientB a n f)).val := by
  apply MeasureTheory.Lp.ext
  have h1 := Multiplication.graphBoundedB_ae (particleTotalEnergy a n)
    (particleTotalEnergy_continuous a n).measurable (bosonicCoreToSector a n f).val
  have h2 := f.val.coeFn_toLp 2 (particleMeasure a n)
  have h3 := (schwartzEnergyCoefficientB a n f.val).coeFn_toLp 2 (particleMeasure a n)
  filter_upwards [h1,h2,h3] with x hx hy hz
  change (Multiplication.graphBoundedB (particleTotalEnergy a n) (particleTotalEnergy_continuous a n).measurable
      (f.val.toLp 2 (particleMeasure a n))) x=
    Multiplication.graphCoefficientB (particleTotalEnergy a n x)*(f.val.toLp 2 (particleMeasure a n)) x at hx
  change (Multiplication.graphBoundedB _ _ (f.val.toLp 2 (particleMeasure a n))) x=
    ((schwartzEnergyCoefficientB a n f.val).toLp 2 (particleMeasure a n)) x
  rw [hx,hy,hz,schwartzEnergyCoefficientB_apply]

end AASCKleinGordon
