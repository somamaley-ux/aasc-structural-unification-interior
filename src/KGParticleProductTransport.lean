import KGSchwartzContraction
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section
open MeasureTheory
namespace AASCKleinGordon

theorem joinParticleCoordinates_measurePreserving (a : Parameters) (n : ℕ) :
    MeasurePreserving (joinParticleCoordinates n)
      ((wignerMeasure a).prod (particleMeasure a n)) (particleMeasure a (n+1)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Momentum) 0
  have h : MeasurePreserving e (particleMeasure a (n+1))
      ((wignerMeasure a).prod (particleMeasure a n)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => wignerMeasure a) 0
  have he : (e.symm : Momentum × ParticleConfiguration n → ParticleConfiguration (n+1)) =
      joinParticleCoordinates n := by
    funext z
    change Fin.insertNth 0 z.1 z.2 = Fin.cons (α:=fun _ : Fin (n+1) => Momentum) z.1 z.2
    exact Fin.insertNth_zero _ _
  rw [← he]
  exact MeasurePreserving.symm e h

theorem splitParticleCoordinates_measurePreserving (a : Parameters) (n : ℕ) :
    MeasurePreserving (joinParticleCoordinates n).symm (particleMeasure a (n+1))
      ((wignerMeasure a).prod (particleMeasure a n)) := by
  have he : ((joinParticleCoordinates n).symm : ParticleConfiguration (n+1) →
      Momentum × ParticleConfiguration n) =
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Momentum) 0 := by
    funext y
    apply Prod.ext
    · rfl
    · funext i
      simp [MeasurableEquiv.piFinSuccAbove, joinParticleCoordinates, Fin.succAbove_zero]
  rw [he]
  exact measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => wignerMeasure a) 0

end AASCKleinGordon
