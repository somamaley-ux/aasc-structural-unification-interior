import KGNRMomentumContraction
import KGSpatialFourierVolume
import LpMeasureEquivalence

/-! The actual p=2*pi*hbar*xi map, its push-forward measure, and constructive
constant-Jacobian L2 normalization. No Fourier or operator bridge is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped ENNReal SchwartzMap
namespace AASCKleinGordon

def kgPhysicalMomentumLength (a : Parameters) : ℝ := 2 * Real.pi * a.hbar

theorem kg_physical_momentum_length_positive (a : Parameters) :
    0 < kgPhysicalMomentumLength a := by
  have hh := a.hbar_pos
  unfold kgPhysicalMomentumLength
  positivity

def kgPhysicalMomentumScaleEquiv (a : Parameters) : KGSpatialSpace ≃L[ℝ] Momentum where
  toLinearEquiv :=
    { toFun := fun x => momentumEuclidean.symm (kgPhysicalMomentumLength a • x)
      invFun := fun p => (kgPhysicalMomentumLength a)⁻¹ • momentumEuclidean p
      left_inv := by
        intro x
        simp [(kg_physical_momentum_length_positive a).ne']
      right_inv := by
        intro p
        simp [(kg_physical_momentum_length_positive a).ne']
      map_add' := by intro x y; simp [smul_add]
      map_smul' := by intro r x; simp [smul_smul, mul_comm] }
  continuous_toFun := momentumEuclidean.symm.continuous.comp (continuous_const.smul continuous_id)
  continuous_invFun := (continuous_const.smul momentumEuclidean.continuous)

theorem kg_physical_momentum_scale_equiv_apply (a : Parameters) (x : KGSpatialSpace) :
    kgPhysicalMomentumScaleEquiv a x = spatialSpectralMomentumCLM a x := by
  simp [kgPhysicalMomentumScaleEquiv, spatialSpectralMomentumCLM, kgPhysicalMomentumLength]

def kgPhysicalMomentumScale (a : Parameters) : ℝ := (2 * Real.pi * a.hbar) ^ 3

theorem kg_physical_momentum_scale_positive (a : Parameters) :
    0 < kgPhysicalMomentumScale a := by
  have hh := a.hbar_pos
  unfold kgPhysicalMomentumScale
  positivity

def kgPhysicalMomentumMeasure (a : Parameters) : Measure Momentum :=
  ENNReal.ofReal (1 / kgPhysicalMomentumScale a) • volume

abbrev KGPhysicalMomentumHilbert (a : Parameters) := Lp ℂ 2 (kgPhysicalMomentumMeasure a)

theorem kg_physical_momentum_volume_eq_scaled (a : Parameters) :
    (volume : Measure Momentum) =
      ENNReal.ofReal (kgPhysicalMomentumScale a) • kgPhysicalMomentumMeasure a := by
  rw [kgPhysicalMomentumMeasure, smul_smul,
    ← ENNReal.ofReal_mul (kg_physical_momentum_scale_positive a).le]
  simp [(kg_physical_momentum_scale_positive a).ne']

theorem kg_physical_momentum_ae (a : Parameters) {P : Momentum → Prop} :
    (∀ᵐ p ∂kgPhysicalMomentumMeasure a, P p) ↔ ∀ᵐ p ∂(volume : Measure Momentum), P p :=
  Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_ne_zero_iff.mpr
    (one_div_pos.mpr (kg_physical_momentum_scale_positive a)))

theorem kg_physical_momentum_integral (a : Parameters) (f : Momentum → ℂ) :
    (∫ p, f p ∂kgPhysicalMomentumMeasure a) =
      ((1 / kgPhysicalMomentumScale a : ℝ) : ℂ) * ∫ p, f p := by
  rw [kgPhysicalMomentumMeasure, integral_smul_measure, ENNReal.toReal_ofReal
    (one_div_pos.mpr (kg_physical_momentum_scale_positive a)).le]
  rfl

def kgPhysicalMomentumRoot (a : Parameters) : ℝ := Real.sqrt (kgPhysicalMomentumScale a)

theorem kg_physical_momentum_root_positive (a : Parameters) : 0<kgPhysicalMomentumRoot a :=
  Real.sqrt_pos.mpr (kg_physical_momentum_scale_positive a)

theorem kg_physical_momentum_root_sq (a : Parameters) : (kgPhysicalMomentumRoot a)^2=kgPhysicalMomentumScale a :=
  Real.sq_sqrt (kg_physical_momentum_scale_positive a).le

def kgPhysicalMomentumForwardMemLp (a : Parameters) (f : KGNRMomentumHilbert) :
    MemLp (fun p => (kgPhysicalMomentumRoot a : ℂ)*f p) 2 (kgPhysicalMomentumMeasure a) :=
  ((Lp.memLp f).smul_measure (c:=ENNReal.ofReal (1/kgPhysicalMomentumScale a))
    ENNReal.ofReal_ne_top).const_mul _

def kgPhysicalMomentumForward (a : Parameters) (f : KGNRMomentumHilbert) : KGPhysicalMomentumHilbert a :=
  (kgPhysicalMomentumForwardMemLp a f).toLp _

theorem kg_physical_momentum_forward_ae (a : Parameters) (f : KGNRMomentumHilbert) :
    kgPhysicalMomentumForward a f=ᵐ[kgPhysicalMomentumMeasure a]
      (fun p => (kgPhysicalMomentumRoot a : ℂ)*f p) :=
  (kgPhysicalMomentumForwardMemLp a f).coeFn_toLp

def kgPhysicalMomentumInverseMemLp (a : Parameters) (f : KGPhysicalMomentumHilbert a) :
    MemLp (fun p => (kgPhysicalMomentumRoot a : ℂ)⁻¹*f p) 2 ((volume : Measure Momentum)) := by
  rw [kg_physical_momentum_volume_eq_scaled a]
  exact ((Lp.memLp f).smul_measure (c:=ENNReal.ofReal (kgPhysicalMomentumScale a))
    ENNReal.ofReal_ne_top).const_mul _

def kgPhysicalMomentumInverse (a : Parameters) (f : KGPhysicalMomentumHilbert a) : KGNRMomentumHilbert :=
  (kgPhysicalMomentumInverseMemLp a f).toLp _

theorem kg_physical_momentum_inverse_ae (a : Parameters) (f : KGPhysicalMomentumHilbert a) :
    kgPhysicalMomentumInverse a f=ᵐ[(volume : Measure Momentum)]
      (fun p => (kgPhysicalMomentumRoot a : ℂ)⁻¹*f p) :=
  (kgPhysicalMomentumInverseMemLp a f).coeFn_toLp

theorem kg_physical_momentum_inverse_forward (a : Parameters) (f : KGNRMomentumHilbert) :
    kgPhysicalMomentumInverse a (kgPhysicalMomentumForward a f)=f := by
  apply Lp.ext
  filter_upwards [kg_physical_momentum_inverse_ae a (kgPhysicalMomentumForward a f),
    (kg_physical_momentum_ae a).mp (kg_physical_momentum_forward_ae a f)] with p hp hq
  rw [hp,hq]
  have hr : (kgPhysicalMomentumRoot a : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (kg_physical_momentum_root_positive a).ne'
  field_simp

theorem kg_physical_momentum_forward_inverse (a : Parameters) (f : KGPhysicalMomentumHilbert a) :
    kgPhysicalMomentumForward a (kgPhysicalMomentumInverse a f)=f := by
  apply Lp.ext
  filter_upwards [kg_physical_momentum_forward_ae a (kgPhysicalMomentumInverse a f),
    (kg_physical_momentum_ae a).mpr (kg_physical_momentum_inverse_ae a f)] with p hp hq
  rw [hp,hq]
  have hr : (kgPhysicalMomentumRoot a : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (kg_physical_momentum_root_positive a).ne'
  field_simp

theorem kg_physical_momentum_forward_add (a : Parameters) (f g : KGNRMomentumHilbert) :
    kgPhysicalMomentumForward a (f+g)=kgPhysicalMomentumForward a f+kgPhysicalMomentumForward a g := by
  apply Lp.ext
  filter_upwards [kg_physical_momentum_forward_ae a (f+g),kg_physical_momentum_forward_ae a f,
    kg_physical_momentum_forward_ae a g,Lp.coeFn_add (kgPhysicalMomentumForward a f) (kgPhysicalMomentumForward a g),
    (kg_physical_momentum_ae a).mpr (Lp.coeFn_add f g)] with p hp hf hg ht hs
  simp only [Pi.add_apply] at hs ht
  rw [hp,ht,hf,hg,hs]
  ring

theorem kg_physical_momentum_forward_smul (a : Parameters) (c : ℂ) (f : KGNRMomentumHilbert) :
    kgPhysicalMomentumForward a (c • f)=c • kgPhysicalMomentumForward a f := by
  apply Lp.ext
  filter_upwards [kg_physical_momentum_forward_ae a (c • f),kg_physical_momentum_forward_ae a f,
    Lp.coeFn_smul c (kgPhysicalMomentumForward a f),(kg_physical_momentum_ae a).mpr (Lp.coeFn_smul c f)]
      with p hp hf ht hs
  simp only [Pi.smul_apply,smul_eq_mul] at hs ht
  rw [hp,ht,hf,hs]
  ring

theorem kg_physical_momentum_forward_inner (a : Parameters) (f g : KGNRMomentumHilbert) :
    inner ℂ (kgPhysicalMomentumForward a f) (kgPhysicalMomentumForward a g)=inner ℂ f g := by
  rw [L2.inner_def,L2.inner_def]
  calc
    _ = ∫ p,(kgPhysicalMomentumScale a : ℂ)*inner ℂ (f p) (g p) ∂kgPhysicalMomentumMeasure a := by
      apply integral_congr_ae
      filter_upwards [kg_physical_momentum_forward_ae a f,kg_physical_momentum_forward_ae a g] with p hp hq
      rw [hp,hq]
      rw [RCLike.inner_apply',RCLike.inner_apply']
      simp only [map_mul,starRingEnd_apply]
      rw [show star (kgPhysicalMomentumRoot a : ℂ)=(kgPhysicalMomentumRoot a : ℂ) from Complex.conj_ofReal _]
      have hsq : (kgPhysicalMomentumRoot a : ℂ)^2=(kgPhysicalMomentumScale a : ℂ) := by
        exact_mod_cast kg_physical_momentum_root_sq a
      linear_combination (star (f p)*g p)*hsq
    _ = _ := by
      rw [kg_physical_momentum_integral,integral_const_mul]
      have hk : (kgPhysicalMomentumScale a : ℂ)≠0 :=
        Complex.ofReal_ne_zero.mpr (kg_physical_momentum_scale_positive a).ne'
      push_cast
      field_simp

def kgPhysicalMomentumNormalization (a : Parameters) :
    KGNRMomentumHilbert ≃ₗᵢ[ℂ] KGPhysicalMomentumHilbert a where
  toFun := kgPhysicalMomentumForward a
  invFun := kgPhysicalMomentumInverse a
  left_inv := kg_physical_momentum_inverse_forward a
  right_inv := kg_physical_momentum_forward_inverse a
  map_add' := kg_physical_momentum_forward_add a
  map_smul' := kg_physical_momentum_forward_smul a
  norm_map' f := by
    change ‖kgPhysicalMomentumForward a f‖=‖f‖
    have h := congrArg Complex.re (kg_physical_momentum_forward_inner a f f)
    have hs : ‖kgPhysicalMomentumForward a f‖^2=‖f‖^2 := by
      calc
        _ = RCLike.re (inner ℂ (kgPhysicalMomentumForward a f) (kgPhysicalMomentumForward a f)) :=
          norm_sq_eq_re_inner (𝕜:=ℂ) _
        _ = RCLike.re (inner ℂ f f) := h
        _ = _ := (norm_sq_eq_re_inner (𝕜:=ℂ) f).symm
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs


end AASCKleinGordon
