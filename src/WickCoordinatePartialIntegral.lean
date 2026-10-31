import WickWignerWeightSchwartz

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

variable {E F V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (μ : Measure E) [μ.HasTemperateGrowth] (T : E ≃L[ℝ] V)

def wickCoordinatePartialPolynomial (x : E) : ℂ := ((1+‖T x‖^2)^μ.integrablePower : ℝ)
def wickCoordinatePartialWeight (x : E) : ℂ := (wickCoordinatePartialPolynomial μ T x)⁻¹

theorem wick_coordinate_partial_nonzero (x : E) : wickCoordinatePartialPolynomial μ T x≠0 := by
  unfold wickCoordinatePartialPolynomial
  exact_mod_cast (pow_pos (by positivity : (0:ℝ)<1+‖T x‖^2) μ.integrablePower).ne'

theorem wick_coordinate_partial_weight_integrable : Integrable (wickCoordinatePartialWeight μ T) μ := by
  have denom (x : E) : 1≤(1+‖T x‖^2)^μ.integrablePower :=
    one_le_pow₀ (le_add_of_nonneg_right (sq_nonneg _))
  have normval (x : E) : ‖wickCoordinatePartialWeight μ T x‖=((1+‖T x‖^2)^μ.integrablePower)⁻¹ := by
    simp only [wickCoordinatePartialWeight,wickCoordinatePartialPolynomial,norm_inv,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ)≤(1+‖T x‖^2)^μ.integrablePower)]
  have measurable : AEStronglyMeasurable (wickCoordinatePartialWeight μ T) μ := by
    apply Continuous.aestronglyMeasurable
    unfold wickCoordinatePartialWeight wickCoordinatePartialPolynomial
    exact (Complex.continuous_ofReal.comp
      ((continuous_const.add (T.continuous.norm.pow 2)).pow μ.integrablePower)).inv₀
        (fun x => wick_coordinate_partial_nonzero μ T x)
  have bounded (x : E) : ‖wickCoordinatePartialWeight μ T x‖≤1 := by
    rw [normval]
    exact inv_le_one_of_one_le₀ (denom x)
  have weighted (x : E) : ‖x‖^(0+μ.integrablePower)*‖wickCoordinatePartialWeight μ T x‖≤
      ‖T.symm.toContinuousLinearMap‖^μ.integrablePower := by
    rw [normval,zero_add,← div_eq_mul_inv]
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (denom x))).mpr
    have normbound : ‖x‖≤‖T.symm.toContinuousLinearMap‖*‖T x‖ := by
      have bound := T.symm.toContinuousLinearMap.le_opNorm (T x)
      change ‖T.symm (T x)‖≤‖T.symm.toContinuousLinearMap‖*‖T x‖ at bound
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using bound
    calc
      _ ≤ (‖T.symm.toContinuousLinearMap‖*‖T x‖)^μ.integrablePower :=
        pow_le_pow_left₀ (norm_nonneg _) normbound _
      _ = ‖T.symm.toContinuousLinearMap‖^μ.integrablePower*‖T x‖^μ.integrablePower := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (by nlinarith [sq_nonneg (‖T x‖-1)]) _) (by positivity)
  have normint := integrable_of_le_of_pow_mul_le (k:=0) bounded weighted measurable
  simp only [pow_zero,one_mul] at normint
  exact normint.mono' measurable (Filter.Eventually.of_forall (fun _ => le_rfl))

theorem wick_coordinate_partial_polynomial_temperate :
    (fun z : E × F => wickCoordinatePartialPolynomial μ T z.1).HasTemperateGrowth := by
  unfold wickCoordinatePartialPolynomial
  exact Complex.ofRealCLM.hasTemperateGrowth.comp
    (((Function.HasTemperateGrowth.const (1:ℝ)).add
      ((Function.hasTemperateGrowth_norm_sq V).comp
        (T.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ E F)).hasTemperateGrowth)).pow μ.integrablePower)

def wickCoordinatePartialIntegralCLM : 𝓢(E × F,ℂ) →L[ℂ] 𝓢(F,ℂ) :=
  (weightedPartialIntegralCLM (wick_coordinate_partial_weight_integrable μ T)).comp
    (SchwartzMap.smulLeftCLM ℂ (fun z : E × F => wickCoordinatePartialPolynomial μ T z.1))

theorem wick_coordinate_partial_integral_apply (H : 𝓢(E × F,ℂ)) (y : F) :
    wickCoordinatePartialIntegralCLM μ T H y=∫ x,H (x,y) ∂μ := by
  change (∫ x,wickCoordinatePartialWeight μ T x •
    (SchwartzMap.smulLeftCLM ℂ (fun z : E × F => wickCoordinatePartialPolynomial μ T z.1) H) (x,y) ∂μ)=_
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [SchwartzMap.smulLeftCLM_apply_apply (wick_coordinate_partial_polynomial_temperate μ T)]
    simp only [smul_eq_mul,wickCoordinatePartialWeight,← mul_assoc,
      inv_mul_cancel₀ (wick_coordinate_partial_nonzero μ T x),one_mul])

end AASCKleinGordon
