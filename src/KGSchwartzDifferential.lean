import KGSpacetimeSmearing

noncomputable section
open scoped SchwartzMap FourierTransform
open LineDeriv
namespace AASCKleinGordon

def spacetimeCoordinateVector (i : Fin 4) : Spacetime := EuclideanSpace.single i 1

def spacetimePartialCLM (i : Fin 4) : 𝓢(Spacetime,ℂ) →L[ℂ] 𝓢(Spacetime,ℂ) :=
  lineDerivOpCLM ℂ 𝓢(Spacetime,ℂ) (spacetimeCoordinateVector i)

def spacetimeSecondPartialCLM (i : Fin 4) : 𝓢(Spacetime,ℂ) →L[ℂ] 𝓢(Spacetime,ℂ) :=
  (spacetimePartialCLM i).comp (spacetimePartialCLM i)

theorem spacetimePartialCLM_apply (i : Fin 4) (h : 𝓢(Spacetime,ℂ)) (x : Spacetime) :
    spacetimePartialCLM i h x = fderiv ℝ h x (spacetimeCoordinateVector i) := rfl

theorem fourier_spacetimePartial_apply (i : Fin 4) (h : 𝓢(Spacetime,ℂ)) (ξ : Spacetime) :
    (𝓕 (spacetimePartialCLM i h)) ξ =
      ((2*Real.pi*ξ i : ℝ) : ℂ) * Complex.I * (𝓕 h) ξ := by
  change (𝓕 (∂_{spacetimeCoordinateVector i} h)) ξ = _
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  have hg : (fun x : Spacetime => inner ℝ x (spacetimeCoordinateVector i)).HasTemperateGrowth :=
    ((innerSL ℝ).flip (spacetimeCoordinateVector i)).hasTemperateGrowth
  change (2*Real.pi*Complex.I) •
    (SchwartzMap.smulLeftCLM ℂ (fun x : Spacetime =>
      inner ℝ x (spacetimeCoordinateVector i)) (𝓕 h) ξ) = _
  rw [SchwartzMap.smulLeftCLM_apply_apply hg]
  simp only [spacetimeCoordinateVector, EuclideanSpace.inner_single_right, one_mul,
    conj_trivial, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
  change (2*(Real.pi : ℂ)*Complex.I) * ((ξ i : ℂ)*(𝓕 h) ξ) = _
  push_cast
  ring

theorem fourier_spacetimeSecondPartial_apply (i : Fin 4) (h : 𝓢(Spacetime,ℂ)) (ξ : Spacetime) :
    (𝓕 (spacetimeSecondPartialCLM i h)) ξ =
      -(((2*Real.pi*ξ i)^2 : ℝ) : ℂ) * (𝓕 h) ξ := by
  change (𝓕 (spacetimePartialCLM i (spacetimePartialCLM i h))) ξ = _
  rw [fourier_spacetimePartial_apply, fourier_spacetimePartial_apply]
  calc
    _ = Complex.I^2 *
        ((((2*Real.pi*ξ i : ℝ) : ℂ))^2 * (𝓕 h) ξ) := by ring
    _ = _ := by rw [Complex.I_sq]; push_cast; ring

def massWaveNumber (a : Parameters) : ℝ := a.mass*a.speed/a.hbar

/-- In x₀=ct coordinates: ∂₀² - ∂₁² - ∂₂² - ∂₃² + (mc/hbar)². -/
def kleinGordonSchwartzCLM (a : Parameters) : 𝓢(Spacetime,ℂ) →L[ℂ] 𝓢(Spacetime,ℂ) :=
  spacetimeSecondPartialCLM 0 - spacetimeSecondPartialCLM 1 -
    spacetimeSecondPartialCLM 2 - spacetimeSecondPartialCLM 3 +
      ((massWaveNumber a)^2 : ℂ) • ContinuousLinearMap.id ℂ _

def kleinGordonSymbol (a : Parameters) (ξ : Spacetime) : ℝ :=
  (massWaveNumber a)^2 + (2*Real.pi)^2 * (-ξ 0^2 + ξ 1^2 + ξ 2^2 + ξ 3^2)

theorem fourier_kleinGordonSchwartz_apply (a : Parameters) (h : 𝓢(Spacetime,ℂ))
    (ξ : Spacetime) :
    (𝓕 (kleinGordonSchwartzCLM a h)) ξ = (kleinGordonSymbol a ξ : ℂ) * (𝓕 h) ξ := by
  change (FourierTransform.fourierCLM ℂ 𝓢(Spacetime,ℂ))
    (kleinGordonSchwartzCLM a h) ξ = _
  simp only [kleinGordonSchwartzCLM, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_add, map_sub, map_smul,
    SchwartzMap.add_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply]
  simp only [FourierTransform.fourierCLM_apply,
    fourier_spacetimeSecondPartial_apply, kleinGordonSymbol, smul_eq_mul]
  push_cast
  ring

theorem kleinGordonSymbol_neg (a : Parameters) (ξ : Spacetime) :
    kleinGordonSymbol a (-ξ) = kleinGordonSymbol a ξ := by
  simp only [kleinGordonSymbol, PiLp.neg_apply, neg_sq]

end AASCKleinGordon
