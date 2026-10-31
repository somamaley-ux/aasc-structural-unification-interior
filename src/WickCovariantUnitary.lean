import WickCovariantMeasure

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped ENNReal SchwartzMap
namespace AASCKleinGordon

def wickCovariantRoot (a : Parameters) : ℝ := Real.sqrt (wickCovariantScale a)

theorem wick_covariant_root_positive (a : Parameters) : 0<wickCovariantRoot a :=
  Real.sqrt_pos.mpr (wick_covariant_scale_positive a)

theorem wick_covariant_root_sq (a : Parameters) : (wickCovariantRoot a)^2=wickCovariantScale a :=
  Real.sq_sqrt (wick_covariant_scale_positive a).le

def wickCovariantForwardMemLp (a : Parameters) (f : OneParticleHilbert a) :
    MemLp (fun p => (wickCovariantRoot a : ℂ)*f p) 2 (wickCovariantMeasure a) :=
  ((Lp.memLp f).smul_measure (c:=ENNReal.ofReal (1/wickCovariantScale a))
    ENNReal.ofReal_ne_top).const_mul _

def wickCovariantForward (a : Parameters) (f : OneParticleHilbert a) : WickCovariantHilbert a :=
  (wickCovariantForwardMemLp a f).toLp _

theorem wick_covariant_forward_ae (a : Parameters) (f : OneParticleHilbert a) :
    wickCovariantForward a f=ᵐ[wickCovariantMeasure a]
      (fun p => (wickCovariantRoot a : ℂ)*f p) :=
  (wickCovariantForwardMemLp a f).coeFn_toLp

def wickCovariantInverseMemLp (a : Parameters) (f : WickCovariantHilbert a) :
    MemLp (fun p => (wickCovariantRoot a : ℂ)⁻¹*f p) 2 (wignerMeasure a) := by
  rw [wick_wigner_eq_scaled_covariant a]
  exact ((Lp.memLp f).smul_measure (c:=ENNReal.ofReal (wickCovariantScale a))
    ENNReal.ofReal_ne_top).const_mul _

def wickCovariantInverse (a : Parameters) (f : WickCovariantHilbert a) : OneParticleHilbert a :=
  (wickCovariantInverseMemLp a f).toLp _

theorem wick_covariant_inverse_ae (a : Parameters) (f : WickCovariantHilbert a) :
    wickCovariantInverse a f=ᵐ[wignerMeasure a]
      (fun p => (wickCovariantRoot a : ℂ)⁻¹*f p) :=
  (wickCovariantInverseMemLp a f).coeFn_toLp

theorem wick_covariant_inverse_forward (a : Parameters) (f : OneParticleHilbert a) :
    wickCovariantInverse a (wickCovariantForward a f)=f := by
  apply Lp.ext
  filter_upwards [wick_covariant_inverse_ae a (wickCovariantForward a f),
    (wick_covariant_ae a).mp (wick_covariant_forward_ae a f)] with p hp hq
  rw [hp,hq]
  have hr : (wickCovariantRoot a : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (wick_covariant_root_positive a).ne'
  field_simp

theorem wick_covariant_forward_inverse (a : Parameters) (f : WickCovariantHilbert a) :
    wickCovariantForward a (wickCovariantInverse a f)=f := by
  apply Lp.ext
  filter_upwards [wick_covariant_forward_ae a (wickCovariantInverse a f),
    (wick_covariant_ae a).mpr (wick_covariant_inverse_ae a f)] with p hp hq
  rw [hp,hq]
  have hr : (wickCovariantRoot a : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (wick_covariant_root_positive a).ne'
  field_simp

theorem wick_covariant_forward_add (a : Parameters) (f g : OneParticleHilbert a) :
    wickCovariantForward a (f+g)=wickCovariantForward a f+wickCovariantForward a g := by
  apply Lp.ext
  filter_upwards [wick_covariant_forward_ae a (f+g),wick_covariant_forward_ae a f,
    wick_covariant_forward_ae a g,Lp.coeFn_add (wickCovariantForward a f) (wickCovariantForward a g),
    (wick_covariant_ae a).mpr (Lp.coeFn_add f g)] with p hp hf hg ht hs
  simp only [Pi.add_apply] at hs ht
  rw [hp,ht,hf,hg,hs]
  ring

theorem wick_covariant_forward_smul (a : Parameters) (c : ℂ) (f : OneParticleHilbert a) :
    wickCovariantForward a (c • f)=c • wickCovariantForward a f := by
  apply Lp.ext
  filter_upwards [wick_covariant_forward_ae a (c • f),wick_covariant_forward_ae a f,
    Lp.coeFn_smul c (wickCovariantForward a f),(wick_covariant_ae a).mpr (Lp.coeFn_smul c f)]
      with p hp hf ht hs
  simp only [Pi.smul_apply,smul_eq_mul] at hs ht
  rw [hp,ht,hf,hs]
  ring

theorem wick_covariant_forward_inner (a : Parameters) (f g : OneParticleHilbert a) :
    inner ℂ (wickCovariantForward a f) (wickCovariantForward a g)=inner ℂ f g := by
  rw [L2.inner_def,L2.inner_def]
  calc
    _ = ∫ p,(wickCovariantScale a : ℂ)*inner ℂ (f p) (g p) ∂wickCovariantMeasure a := by
      apply integral_congr_ae
      filter_upwards [wick_covariant_forward_ae a f,wick_covariant_forward_ae a g] with p hp hq
      rw [hp,hq]
      rw [RCLike.inner_apply',RCLike.inner_apply']
      simp only [map_mul,starRingEnd_apply]
      rw [show star (wickCovariantRoot a : ℂ)=(wickCovariantRoot a : ℂ) from Complex.conj_ofReal _]
      have hsq : (wickCovariantRoot a : ℂ)^2=(wickCovariantScale a : ℂ) := by
        exact_mod_cast wick_covariant_root_sq a
      linear_combination (star (f p)*g p)*hsq
    _ = _ := by
      rw [wick_covariant_integral,integral_const_mul]
      have hk : (wickCovariantScale a : ℂ)≠0 :=
        Complex.ofReal_ne_zero.mpr (wick_covariant_scale_positive a).ne'
      push_cast
      field_simp

def wickCovariantNormalization (a : Parameters) :
    OneParticleHilbert a ≃ₗᵢ[ℂ] WickCovariantHilbert a where
  toFun := wickCovariantForward a
  invFun := wickCovariantInverse a
  left_inv := wick_covariant_inverse_forward a
  right_inv := wick_covariant_forward_inverse a
  map_add' := wick_covariant_forward_add a
  map_smul' := wick_covariant_forward_smul a
  norm_map' f := by
    change ‖wickCovariantForward a f‖=‖f‖
    have h := congrArg Complex.re (wick_covariant_forward_inner a f f)
    have hs : ‖wickCovariantForward a f‖^2=‖f‖^2 := by
      calc
        _ = RCLike.re (inner ℂ (wickCovariantForward a f) (wickCovariantForward a f)) :=
          norm_sq_eq_re_inner (𝕜:=ℂ) _
        _ = RCLike.re (inner ℂ f f) := h
        _ = _ := (norm_sq_eq_re_inner (𝕜:=ℂ) f).symm
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

def wickCovariantSchwartz (a : Parameters) (f : 𝓢(Momentum,ℂ)) : 𝓢(Momentum,ℂ) :=
  (wickCovariantRoot a : ℂ) • f

theorem wick_covariant_normalization_schwartz_ae (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    wickCovariantNormalization a (oneParticleSchwartzToHilbert a f)=ᵐ[wickCovariantMeasure a]
      wickCovariantSchwartz a f := by
  filter_upwards [wick_covariant_forward_ae a (oneParticleSchwartzToHilbert a f),
    (wick_covariant_ae a).mpr (f.coeFn_toLp 2 (wignerMeasure a))] with p hp hq
  change wickCovariantForward a (oneParticleSchwartzToHilbert a f) p=_
  rw [hp]
  change (wickCovariantRoot a : ℂ)*(f.toLp 2 (wignerMeasure a)) p=
    (wickCovariantRoot a : ℂ)*f p
  rw [hq]

end AASCKleinGordon
