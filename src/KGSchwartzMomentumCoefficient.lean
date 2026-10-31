import KGBosonicMaximalMultiplication
import Mathlib.Analysis.Distribution.TemperateGrowth

noncomputable section
open scoped SchwartzMap
namespace AASCKleinGordon

theorem graphCoefficientB_rpow (r : ℝ) :
    Multiplication.graphCoefficientB r=((1+‖r‖^2)^(-(1/(2:ℝ))) : ℝ) := by
  simp only [Multiplication.graphCoefficientB,Multiplication.graphDenominator]
  rw [Real.rpow_neg (by positivity),← Real.sqrt_eq_rpow]
  simp [Real.norm_eq_abs,sq_abs,one_div]

theorem graphCoefficientB_temperate : Multiplication.graphCoefficientB.HasTemperateGrowth := by
  have hreal := Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (-(1/(2:ℝ)))
  have h := Complex.ofRealCLM.hasTemperateGrowth.comp hreal
  have he : Multiplication.graphCoefficientB=Complex.ofReal ∘
      (fun r : ℝ => (1+‖r‖^2)^(-(1/(2:ℝ)))) := funext graphCoefficientB_rpow
  rw [he]
  exact h

theorem momentumCoefficientB_temperate (n : ℕ) (j : Fin 3) :
    (fun x => Multiplication.graphCoefficientB (totalMomentumCLM n j x)).HasTemperateGrowth :=
  graphCoefficientB_temperate.comp (totalMomentumCLM n j).hasTemperateGrowth

def schwartzMomentumCoefficientB (n : ℕ) (j : Fin 3) :
    𝓢(ParticleConfiguration n,ℂ) →L[ℂ] 𝓢(ParticleConfiguration n,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x => Multiplication.graphCoefficientB (totalMomentumCLM n j x))

theorem schwartzMomentumCoefficientB_apply (n : ℕ) (j : Fin 3)
    (f : 𝓢(ParticleConfiguration n,ℂ)) (x : ParticleConfiguration n) :
    schwartzMomentumCoefficientB n j f x=
      Multiplication.graphCoefficientB (totalMomentumCLM n j x)*f x :=
  SchwartzMap.smulLeftCLM_apply_apply (momentumCoefficientB_temperate n j) f x

def bosonicSchwartzMomentumCoefficientB (n : ℕ) (j : Fin 3) :
    bosonicSchwartz n →ₗ[ℂ] bosonicSchwartz n where
  toFun f := ⟨schwartzMomentumCoefficientB n j f.val,by
    intro σ x
    rw [schwartzMomentumCoefficientB_apply,schwartzMomentumCoefficientB_apply,
      totalMomentum_permutation,f.property]⟩
  map_add' f g := by apply Subtype.ext; exact (schwartzMomentumCoefficientB n j).map_add f.val g.val
  map_smul' c f := by apply Subtype.ext; exact (schwartzMomentumCoefficientB n j).map_smul c f.val

theorem bosonicMomentumCoefficientB_intertwines (a : Parameters) (n : ℕ) (j : Fin 3)
    (f : bosonicSchwartz n) :
    Multiplication.graphBoundedB (totalMomentumCLM n j) (totalMomentumCLM n j).measurable
        (bosonicCoreToSector a n f).val=
      (bosonicCoreToSector a n (bosonicSchwartzMomentumCoefficientB n j f)).val := by
  apply MeasureTheory.Lp.ext
  have h1 := Multiplication.graphBoundedB_ae (totalMomentumCLM n j)
    (totalMomentumCLM n j).measurable (bosonicCoreToSector a n f).val
  have h2 := f.val.coeFn_toLp 2 (particleMeasure a n)
  have h3 := (schwartzMomentumCoefficientB n j f.val).coeFn_toLp 2 (particleMeasure a n)
  filter_upwards [h1,h2,h3] with x hx hy hz
  change (Multiplication.graphBoundedB (totalMomentumCLM n j) (totalMomentumCLM n j).measurable
      (f.val.toLp 2 (particleMeasure a n))) x=
    Multiplication.graphCoefficientB (totalMomentumCLM n j x)*(f.val.toLp 2 (particleMeasure a n)) x at hx
  change (Multiplication.graphBoundedB _ _ (f.val.toLp 2 (particleMeasure a n))) x=
    ((schwartzMomentumCoefficientB n j f.val).toLp 2 (particleMeasure a n)) x
  rw [hx,hy,hz,schwartzMomentumCoefficientB_apply]

end AASCKleinGordon
