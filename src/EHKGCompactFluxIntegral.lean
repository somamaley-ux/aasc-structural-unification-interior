import EHKGScalarActionVariation
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Compact variation flux has zero integrated divergence. This is proved
from the actual derivative by integration by parts, not supplied as a boundary
certificate. The actual globally smooth compact EH factor is used. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open scoped Topology BigOperators
namespace AASCKleinGordon.CurvedKG

theorem smooth_compact_scalar_partial_integral_zero (F : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ (⊤ : ℕ∞) F) (compact : HasCompactSupport F) (i : Fin 4) :
    (∫ p : CoordinatePoint, scalarPartial F p i) = 0 := by
  obtain ⟨C, lipschitz⟩ := ContDiff.lipschitzWith_of_hasCompactSupport compact regular (by simp)
  have constantLipschitz : LipschitzWith 0 (fun _ : CoordinatePoint => (1 : ℝ)) := by
    intro p q
    simp
  have parts := constantLipschitz.integral_lineDeriv_mul_eq (μ := (volume : Measure CoordinatePoint))
    lipschitz compact (-(Pi.single i (1 : ℝ) : CoordinatePoint))
  have constantDerivative (p : CoordinatePoint) :
      lineDeriv ℝ (fun _ : CoordinatePoint => (1 : ℝ)) p (-(Pi.single i (1 : ℝ) : CoordinatePoint)) = 0 := by
    have differentiable : DifferentiableAt ℝ (fun _ : CoordinatePoint => (1 : ℝ)) p := by fun_prop
    rw [differentiable.lineDeriv_eq_fderiv]
    simp
  simp only [constantDerivative, zero_mul, integral_zero, neg_neg, mul_one] at parts
  have actual : (fun p : CoordinatePoint => lineDeriv ℝ F p (Pi.single i (1 : ℝ))) =
      (fun p => scalarPartial F p i) := by
    funext p
    exact (regular.differentiable (by simp) p).lineDeriv_eq_fderiv
  simpa only [actual] using parts.symm

theorem smooth_compact_scalar_partial_integrable (F : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ (⊤ : ℕ∞) F) (compact : HasCompactSupport F) (i : Fin 4) :
    Integrable (fun p => scalarPartial F p i) := by
  have compactFirst := (compact.fderiv ℝ).comp_left
    (g := fun D : CoordinatePoint →L[ℝ] ℝ => D (Pi.single i (1 : ℝ))) (by simp)
  exact (scalar_partial_smooth F regular i).continuous.integrable_of_hasCompactSupport compactFirst

def actualScalarVariationFlux (a : Parameters) (u d : CoordinatePoint → ℝ)
    (i : Fin 4) (p : CoordinatePoint) : ℝ :=
  ((if i = 0 then 1 else -1) * conformalMetricFactor (conformalFrequency a) p * scalarPartial u p i) * d p

theorem actual_scalar_variation_flux_smooth (a : Parameters) (u d : CoordinatePoint → ℝ)
    (regularU : ContDiff ℝ (⊤ : ℕ∞) u) (regularD : ContDiff ℝ (⊤ : ℕ∞) d) (i : Fin 4) :
    ContDiff ℝ (⊤ : ℕ∞) (actualScalarVariationFlux a u d i) :=
  ((contDiff_const.mul (contDiff_const.add (conformalProfile (conformalFrequency a)).contDiff)).mul
    (scalar_partial_smooth u regularU i)).mul regularD

theorem actual_scalar_variation_flux_compact (a : Parameters) (u d : CoordinatePoint → ℝ)
    (compactD : HasCompactSupport d) (i : Fin 4) :
    HasCompactSupport (actualScalarVariationFlux a u d i) := compactD.mul_left

def actualScalarVariationDivergence (a : Parameters) (u d : CoordinatePoint → ℝ)
    (p : CoordinatePoint) : ℝ := ∑ i : Fin 4, scalarPartial (actualScalarVariationFlux a u d i) p i

theorem actual_scalar_variation_divergence_integral_zero (a : Parameters) (u d : CoordinatePoint → ℝ)
    (regularU : ContDiff ℝ (⊤ : ℕ∞) u) (regularD : ContDiff ℝ (⊤ : ℕ∞) d)
    (compactD : HasCompactSupport d) :
    (∫ p : CoordinatePoint, actualScalarVariationDivergence a u d p) = 0 := by
  unfold actualScalarVariationDivergence
  rw [integral_finset_sum _ (fun i hi => smooth_compact_scalar_partial_integrable _
    (actual_scalar_variation_flux_smooth a u d regularU regularD i)
    (actual_scalar_variation_flux_compact a u d compactD i) i)]
  simp only [smooth_compact_scalar_partial_integral_zero _
    (actual_scalar_variation_flux_smooth a u d regularU regularD _)
    (actual_scalar_variation_flux_compact a u d compactD _) _, Finset.sum_const_zero]

end AASCKleinGordon.CurvedKG
