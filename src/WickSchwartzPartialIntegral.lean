import SchwartzWeightedIntegral
import WickOriginalChargeKernels

/-! Actual unweighted partial integration preserves Schwartz regularity.
The integrable auxiliary weight cancels identically; no charge-density
regularity or Fourier diagonal certificate is received as a premise. -/
noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (μ : Measure E) [μ.HasTemperateGrowth]

def wickPartialPolynomial (x : E) : ℂ := ((1+‖x‖^2)^μ.integrablePower : ℝ)

def wickPartialWeight (x : E) : ℂ := (wickPartialPolynomial μ x)⁻¹

theorem wick_partial_polynomial_nonzero (x : E) : wickPartialPolynomial μ x≠0 := by
  unfold wickPartialPolynomial
  exact_mod_cast (pow_pos (by positivity : (0:ℝ)<1+‖x‖^2) μ.integrablePower).ne'

theorem wick_partial_weight_integrable : Integrable (wickPartialWeight μ) μ := by
  have denom (x : E) : 1≤(1+‖x‖^2)^μ.integrablePower :=
    one_le_pow₀ (le_add_of_nonneg_right (sq_nonneg _))
  have normval (x : E) : ‖wickPartialWeight μ x‖=((1+‖x‖^2)^μ.integrablePower)⁻¹ := by
    simp only [wickPartialWeight, wickPartialPolynomial, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ)≤(1+‖x‖^2)^μ.integrablePower)]
  have measurable : AEStronglyMeasurable (wickPartialWeight μ) μ := by
    apply Continuous.aestronglyMeasurable
    unfold wickPartialWeight wickPartialPolynomial
    exact ((Complex.continuous_ofReal.comp
      ((continuous_const.add (continuous_norm.pow 2)).pow μ.integrablePower))).inv₀
        (fun x => wick_partial_polynomial_nonzero μ x)
  have bounded (x : E) : ‖wickPartialWeight μ x‖≤1 := by
    rw [normval]
    exact inv_le_one_of_one_le₀ (denom x)
  have weighted (x : E) : ‖x‖^(0+μ.integrablePower)*‖wickPartialWeight μ x‖≤1 := by
    rw [normval, zero_add, ← div_eq_mul_inv]
    apply (div_le_one (lt_of_lt_of_le zero_lt_one (denom x))).mpr
    apply pow_le_pow_left₀ (norm_nonneg _)
    nlinarith [sq_nonneg (‖x‖-1)]
  have normint := integrable_of_le_of_pow_mul_le (k:=0) bounded weighted measurable
  simp only [pow_zero, one_mul] at normint
  exact normint.mono' measurable (Filter.Eventually.of_forall (fun _ => le_rfl))

theorem wick_partial_polynomial_temperate :
    (fun z : E × F => wickPartialPolynomial μ z.1).HasTemperateGrowth := by
  unfold wickPartialPolynomial
  exact Complex.ofRealCLM.hasTemperateGrowth.comp
    (((Function.HasTemperateGrowth.const (1:ℝ)).add
      ((Function.hasTemperateGrowth_norm_sq E).comp
        (ContinuousLinearMap.fst ℝ E F).hasTemperateGrowth)).pow μ.integrablePower)

def wickSchwartzPartialIntegralCLM : 𝓢(E × F,ℂ) →L[ℂ] 𝓢(F,ℂ) :=
  (weightedPartialIntegralCLM (wick_partial_weight_integrable μ)).comp
    (SchwartzMap.smulLeftCLM ℂ (fun z : E × F => wickPartialPolynomial μ z.1))

theorem wick_schwartz_partial_integral_apply (H : 𝓢(E × F,ℂ)) (y : F) :
    wickSchwartzPartialIntegralCLM μ H y=∫ x,H (x,y) ∂μ := by
  change (∫ x,wickPartialWeight μ x •
    (SchwartzMap.smulLeftCLM ℂ (fun z : E × F => wickPartialPolynomial μ z.1) H) (x,y) ∂μ)=_
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [SchwartzMap.smulLeftCLM_apply_apply (wick_partial_polynomial_temperate μ)]
    simp only [smul_eq_mul, wickPartialWeight, ← mul_assoc,
      inv_mul_cancel₀ (wick_partial_polynomial_nonzero μ x), one_mul])

theorem wick_schwartz_partial_slice_integrable (H : 𝓢(E × F,ℂ)) (y : F) :
    Integrable (fun x => H (x,y)) μ := by
  have integral := weighted_slice_integrable (wick_partial_weight_integrable μ)
    (SchwartzMap.smulLeftCLM ℂ (fun z : E × F => wickPartialPolynomial μ z.1) H) y
  convert integral using 1
  funext x
  rw [SchwartzMap.smulLeftCLM_apply_apply (wick_partial_polynomial_temperate μ)]
  simp only [smul_eq_mul, wickPartialWeight, ← mul_assoc,
    inv_mul_cancel₀ (wick_partial_polynomial_nonzero μ x), one_mul]

end AASCKleinGordon
