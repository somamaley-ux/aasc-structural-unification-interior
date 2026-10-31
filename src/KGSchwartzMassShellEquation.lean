import KGSchwartzDifferential
import SchwartzFourierConjugation

noncomputable section
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon
open SchwartzOperations

theorem fourCoordinateJoin_apply (t : ℝ) (p : Momentum) (i : Fin 4) :
    fourCoordinateJoin (t,p) i = Fin.cons (α := fun _ : Fin 4 => ℝ) t p i := rfl

theorem shellFrequency_apply (a : Parameters) (p : Momentum) (i : Fin 4) :
    shellFrequency a p i = fourierWaveScale a *
      Fin.cons (α := fun _ : Fin 4 => ℝ) (-energy a p/a.speed) p i := by
  rw [shellFrequency, shellCovector_eq_join]
  rfl

theorem two_pi_fourierWaveScale (a : Parameters) :
    (2*Real.pi)*fourierWaveScale a = a.hbar⁻¹ := by
  dsimp [fourierWaveScale]
  field_simp

theorem kleinGordonSymbol_on_shell (a : Parameters) (p : Momentum) :
    kleinGordonSymbol a (shellFrequency a p) = 0 := by
  have hs : -(energy a p/a.speed)^2 + p 0^2 + p 1^2 + p 2^2 =
      -(a.mass^2*a.speed^2) := by
    simpa only [massShell, minkowskiDot, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, pow_two] using massShell_on_shell a p
  simp only [kleinGordonSymbol, shellFrequency_apply, Fin.cons_zero]
  change (massWaveNumber a)^2 + (2*Real.pi)^2 *
    (-(fourierWaveScale a * (-energy a p/a.speed))^2 +
      (fourierWaveScale a * p 0)^2 + (fourierWaveScale a * p 1)^2 +
      (fourierWaveScale a * p 2)^2) = 0
  calc
    _ = (massWaveNumber a)^2 + ((2*Real.pi)*fourierWaveScale a)^2 *
        (-(energy a p/a.speed)^2 + p 0^2 + p 1^2 + p 2^2) := by ring
    _ = (massWaveNumber a)^2 + (a.hbar⁻¹)^2 * (-(a.mass^2*a.speed^2)) := by
      rw [two_pi_fourierWaveScale, hs]
    _ = 0 := by dsimp [massWaveNumber]; field_simp; ring

theorem spacetimeSmearing_kleinGordon_zero (a : Parameters) (h : 𝓢(Spacetime,ℂ)) :
    spacetimeSmearingCLM a (kleinGordonSchwartzCLM a h) = 0 := by
  ext p
  rw [spacetimeSmearingCLM_apply, fourier_kleinGordonSchwartz_apply,
    kleinGordonSymbol_on_shell]
  simp

theorem spacetimeSmearing_conjugate_kleinGordon_zero (a : Parameters)
    (h : 𝓢(Spacetime,ℂ)) :
    spacetimeSmearingCLM a (conjugateSchwartzCLM (kleinGordonSchwartzCLM a h)) = 0 := by
  ext p
  rw [spacetimeSmearingCLM_apply, fourier_conjugateSchwartz_apply,
    fourier_kleinGordonSchwartz_apply, kleinGordonSymbol_neg,
    kleinGordonSymbol_on_shell]
  simp

theorem conjugate_kleinGordon_commute (a : Parameters) (h : 𝓢(Spacetime,ℂ)) :
    conjugateSchwartzCLM (kleinGordonSchwartzCLM a h) =
      kleinGordonSchwartzCLM a (conjugateSchwartzCLM h) := by
  apply (FourierTransform.fourierCLE ℂ 𝓢(Spacetime,ℂ)).injective
  ext ξ
  change (𝓕 (conjugateSchwartzCLM (kleinGordonSchwartzCLM a h))) ξ =
    (𝓕 (kleinGordonSchwartzCLM a (conjugateSchwartzCLM h))) ξ
  rw [fourier_conjugateSchwartz_apply, fourier_kleinGordonSchwartz_apply,
    fourier_kleinGordonSchwartz_apply, fourier_conjugateSchwartz_apply,
    kleinGordonSymbol_neg]
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal, mul_comm]

end AASCKleinGordon
