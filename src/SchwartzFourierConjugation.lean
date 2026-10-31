import KGSpacetimeSmearing
import SchwartzConjugation

noncomputable section
open MeasureTheory Real
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon
open SchwartzOperations

theorem fourier_conjugateSchwartz_apply (h : 𝓢(Spacetime,ℂ)) (ξ : Spacetime) :
    (𝓕 (conjugateSchwartzCLM h)) ξ = star ((𝓕 h) (-ξ)) := by
  change 𝓕 (fun x => star (h x)) ξ = star (𝓕 (h : Spacetime → ℂ) (-ξ))
  simp_rw [fourier_eq', smul_eq_mul]
  change (∫ v : Spacetime, Complex.exp (↑(-2 * π * inner ℝ v ξ) * Complex.I) * star (h v)) =
    (starRingEnd ℂ) (∫ v : Spacetime,
      Complex.exp (↑(-2 * π * inner ℝ v (-ξ)) * Complex.I) * h v)
  rw [← integral_conj]
  apply integral_congr_ae
  exact ae_of_all volume fun x => by
    simp only [map_mul, ← Complex.exp_conj, map_mul, inner_neg_right,
      Complex.conj_ofReal, Complex.conj_I]
    congr 1
    congr 1
    push_cast
    ring

end AASCKleinGordon
