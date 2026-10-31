import KGNRMomentumContraction
import KGOneParticleHilbert

/-! The actual positive-density identification of the isolated scalar carrier.
The reciprocal multiplier is justified between the two measures; it is not
assumed to be a bounded multiplier on flat L2. No standing, spatial generator,
curved-background or Einstein/source bridge is assumed or concluded here. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped ENNReal
namespace AASCKleinGordon

def kgWignerRoot (a : Parameters) (p : Momentum) : ℝ := Real.sqrt (wignerWeight a p)

theorem kg_wigner_root_pos (a : Parameters) (p : Momentum) : 0 < kgWignerRoot a p :=
  Real.sqrt_pos.mpr (wignerWeight_pos a p)

theorem kg_wigner_root_sq (a : Parameters) (p : Momentum) :
    kgWignerRoot a p ^ 2 = wignerWeight a p :=
  Real.sq_sqrt (wignerWeight_pos a p).le

theorem kg_wigner_root_continuous (a : Parameters) : Continuous (kgWignerRoot a) :=
  (wignerWeight_continuous a).sqrt

theorem kg_wigner_ae (a : Parameters) {P : Momentum → Prop} :
    (∀ᵐ p ∂wignerMeasure a, P p) ↔ ∀ᵐ p ∂(volume : Measure Momentum), P p :=
  ⟨fun h => h.filter_mono (volume_absolutelyContinuous_wigner a).ae_le,
   fun h => h.filter_mono (withDensity_absolutelyContinuous volume (wignerDensity a)).ae_le⟩

theorem kg_wigner_integrable_iff (a : Parameters) (g : Momentum → ℝ) :
    Integrable g (wignerMeasure a) ↔
      Integrable (fun p => wignerWeight a p * g p) volume := by
  simpa only [wignerMeasure, wignerDensity, ENNReal.toReal_ofReal (wignerWeight_pos a _).le,
    smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure Momentum))
      (wignerDensity_measurable a) (Eventually.of_forall (fun p =>
        ENNReal.ofReal_lt_top : ∀ p, wignerDensity a p < ∞)) (g := g))

theorem kg_wigner_root_norm_sq (a : Parameters) (p : Momentum) (z : ℂ) :
    ‖(kgWignerRoot a p : ℂ) * z‖ ^ 2 = wignerWeight a p * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (kg_wigner_root_pos a p), kg_wigner_root_sq]

theorem kg_wigner_inverse_norm_sq (a : Parameters) (p : Momentum) (z : ℂ) :
    wignerWeight a p * ‖(kgWignerRoot a p : ℂ)⁻¹ * z‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [norm_mul, norm_inv, mul_pow, inv_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (kg_wigner_root_pos a p), kg_wigner_root_sq]
  field_simp [(wignerWeight_pos a p).ne']

def kgWeightedMomentumForwardMemLp (a : Parameters) (f : OneParticleHilbert a) :
    MemLp (fun p => (kgWignerRoot a p : ℂ) * f p) 2 (volume : Measure Momentum) := by
  have hm : AEStronglyMeasurable (fun p => (kgWignerRoot a p : ℂ) * f p) volume :=
    (Complex.continuous_ofReal.comp (kg_wigner_root_continuous a)).aestronglyMeasurable.mul
      ((Lp.memLp f).aestronglyMeasurable.mono_ac (volume_absolutelyContinuous_wigner a))
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  simpa only [kg_wigner_root_norm_sq] using
    (kg_wigner_integrable_iff a (fun p => ‖f p‖ ^ 2)).mp (Lp.memLp f).norm.integrable_sq

def kgWeightedMomentumForward (a : Parameters) (f : OneParticleHilbert a) : KGNRMomentumHilbert :=
  (kgWeightedMomentumForwardMemLp a f).toLp _

theorem kg_weighted_momentum_forward_ae (a : Parameters) (f : OneParticleHilbert a) :
    kgWeightedMomentumForward a f =ᵐ[volume] (fun p => (kgWignerRoot a p : ℂ) * f p) :=
  (kgWeightedMomentumForwardMemLp a f).coeFn_toLp

def kgWeightedMomentumInverseMemLp (a : Parameters) (f : KGNRMomentumHilbert) :
    MemLp (fun p => (kgWignerRoot a p : ℂ)⁻¹ * f p) 2 (wignerMeasure a) := by
  have hr : Continuous (fun p => (kgWignerRoot a p : ℂ)⁻¹) :=
    (Complex.continuous_ofReal.comp (kg_wigner_root_continuous a)).inv₀
      (fun p => Complex.ofReal_ne_zero.mpr (kg_wigner_root_pos a p).ne')
  have hm : AEStronglyMeasurable (fun p => (kgWignerRoot a p : ℂ)⁻¹ * f p)
      (wignerMeasure a) :=
    hr.aestronglyMeasurable.mul ((Lp.memLp f).aestronglyMeasurable.mono_ac
      (withDensity_absolutelyContinuous volume (wignerDensity a)))
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply (kg_wigner_integrable_iff a _).mpr
  simpa only [kg_wigner_inverse_norm_sq] using (Lp.memLp f).norm.integrable_sq

def kgWeightedMomentumInverse (a : Parameters) (f : KGNRMomentumHilbert) : OneParticleHilbert a :=
  (kgWeightedMomentumInverseMemLp a f).toLp _

theorem kg_weighted_momentum_inverse_ae (a : Parameters) (f : KGNRMomentumHilbert) :
    kgWeightedMomentumInverse a f =ᵐ[wignerMeasure a]
      (fun p => (kgWignerRoot a p : ℂ)⁻¹ * f p) :=
  (kgWeightedMomentumInverseMemLp a f).coeFn_toLp

theorem kg_weighted_momentum_inverse_forward (a : Parameters) (f : OneParticleHilbert a) :
    kgWeightedMomentumInverse a (kgWeightedMomentumForward a f) = f := by
  apply Lp.ext
  filter_upwards [kg_weighted_momentum_inverse_ae a (kgWeightedMomentumForward a f),
    (kg_wigner_ae a).mpr (kg_weighted_momentum_forward_ae a f)] with p hp hq
  rw [hp, hq]
  have hr : (kgWignerRoot a p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (kg_wigner_root_pos a p).ne'
  field_simp

theorem kg_weighted_momentum_forward_inverse (a : Parameters) (f : KGNRMomentumHilbert) :
    kgWeightedMomentumForward a (kgWeightedMomentumInverse a f) = f := by
  apply Lp.ext
  filter_upwards [kg_weighted_momentum_forward_ae a (kgWeightedMomentumInverse a f),
    (kg_wigner_ae a).mp (kg_weighted_momentum_inverse_ae a f)] with p hp hq
  rw [hp, hq]
  have hr : (kgWignerRoot a p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (kg_wigner_root_pos a p).ne'
  field_simp

theorem kg_weighted_momentum_forward_add (a : Parameters) (f g : OneParticleHilbert a) :
    kgWeightedMomentumForward a (f + g) =
      kgWeightedMomentumForward a f + kgWeightedMomentumForward a g := by
  apply Lp.ext
  filter_upwards [kg_weighted_momentum_forward_ae a (f + g),
    kg_weighted_momentum_forward_ae a f, kg_weighted_momentum_forward_ae a g,
    Lp.coeFn_add (kgWeightedMomentumForward a f) (kgWeightedMomentumForward a g),
    (kg_wigner_ae a).mp (Lp.coeFn_add f g)] with p hp hf hg ht hs
  simp only [Pi.add_apply] at hs ht
  rw [hp, ht, hf, hg, hs]
  ring

theorem kg_weighted_momentum_forward_smul (a : Parameters) (c : ℂ) (f : OneParticleHilbert a) :
    kgWeightedMomentumForward a (c • f) = c • kgWeightedMomentumForward a f := by
  apply Lp.ext
  filter_upwards [kg_weighted_momentum_forward_ae a (c • f),
    kg_weighted_momentum_forward_ae a f, Lp.coeFn_smul c (kgWeightedMomentumForward a f),
    (kg_wigner_ae a).mp (Lp.coeFn_smul c f)] with p hp hf ht hs
  simp only [Pi.smul_apply, smul_eq_mul] at hs ht
  rw [hp, ht, hf, hs]
  ring

theorem kg_weighted_momentum_forward_inner (a : Parameters) (f g : OneParticleHilbert a) :
    inner ℂ (kgWeightedMomentumForward a f) (kgWeightedMomentumForward a g) = inner ℂ f g := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ p, (wignerWeight a p : ℂ) * inner ℂ (f p) (g p) := by
      apply integral_congr_ae
      filter_upwards [kg_weighted_momentum_forward_ae a f,
        kg_weighted_momentum_forward_ae a g] with p hp hq
      rw [hp, hq, RCLike.inner_apply', RCLike.inner_apply']
      simp only [map_mul, starRingEnd_apply]
      rw [show star (kgWignerRoot a p : ℂ) = (kgWignerRoot a p : ℂ)
        from Complex.conj_ofReal _]
      have hsq : (kgWignerRoot a p : ℂ) ^ 2 = (wignerWeight a p : ℂ) := by
        exact_mod_cast kg_wigner_root_sq a p
      linear_combination (star (f p) * g p) * hsq
    _ = _ := by
      change (∫ p, (wignerWeight a p : ℂ) * inner ℂ (f p) (g p)) =
        ∫ p, inner ℂ (f p) (g p) ∂(volume.withDensity (wignerDensity a))
      rw [integral_withDensity_eq_integral_toReal_smul
        (wignerDensity_measurable a) (Eventually.of_forall (fun p =>
          ENNReal.ofReal_lt_top : ∀ p, wignerDensity a p < ∞))]
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by
        simp only [wignerDensity, ENNReal.toReal_ofReal (wignerWeight_pos a p).le,
          Complex.real_smul])

def kgWeightedMomentumUnitary (a : Parameters) :
    OneParticleHilbert a ≃ₗᵢ[ℂ] KGNRMomentumHilbert where
  toFun := kgWeightedMomentumForward a
  invFun := kgWeightedMomentumInverse a
  left_inv := kg_weighted_momentum_inverse_forward a
  right_inv := kg_weighted_momentum_forward_inverse a
  map_add' := kg_weighted_momentum_forward_add a
  map_smul' := kg_weighted_momentum_forward_smul a
  norm_map' f := by
    change ‖kgWeightedMomentumForward a f‖ = ‖f‖
    have h := congrArg Complex.re (kg_weighted_momentum_forward_inner a f f)
    have hs : ‖kgWeightedMomentumForward a f‖ ^ 2 = ‖f‖ ^ 2 := by
      calc
        _ = RCLike.re (inner ℂ (kgWeightedMomentumForward a f) (kgWeightedMomentumForward a f)) :=
          norm_sq_eq_re_inner (𝕜 := ℂ) _
        _ = RCLike.re (inner ℂ f f) := h
        _ = _ := (norm_sq_eq_re_inner (𝕜 := ℂ) f).symm
    nlinarith [norm_nonneg (kgWeightedMomentumForward a f), norm_nonneg f]

end AASCKleinGordon
