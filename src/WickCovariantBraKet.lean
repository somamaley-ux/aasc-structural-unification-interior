import WickCovariantNaturalTest
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped SchwartzMap
namespace AASCKleinGordon

def wickCovariantBra (a : Parameters) (f : WickCovariantHilbert a) :
    𝓢(Momentum,ℂ) →L[ℂ] ℂ :=
  (innerSL ℂ f).comp (wickCovariantNaturalTest a)

def wickCovariantKet (a : Parameters) (f : WickCovariantHilbert a) :
    𝓢(Momentum,ℂ) →L⋆[ℂ] ℂ :=
  (innerSLFlip ℂ f).comp (wickCovariantNaturalTest a)

theorem wick_covariant_bra_apply (a : Parameters) (f : WickCovariantHilbert a)
    (h : 𝓢(Momentum,ℂ)) :
    wickCovariantBra a f h=inner ℂ f (wickCovariantNaturalTest a h) := rfl

theorem wick_covariant_ket_apply (a : Parameters) (f : WickCovariantHilbert a)
    (h : 𝓢(Momentum,ℂ)) :
    wickCovariantKet a f h=inner ℂ (wickCovariantNaturalTest a h) f := rfl

theorem wick_covariant_bra_state_smul (a : Parameters) (c : ℂ) (f : WickCovariantHilbert a)
    (h : 𝓢(Momentum,ℂ)) :
    wickCovariantBra a (c • f) h=star c*wickCovariantBra a f h := by
  simp only [wick_covariant_bra_apply,inner_smul_left]
  rfl

theorem wick_covariant_ket_state_smul (a : Parameters) (c : ℂ) (f : WickCovariantHilbert a)
    (h : 𝓢(Momentum,ℂ)) :
    wickCovariantKet a (c • f) h=c*wickCovariantKet a f h := by
  simp only [wick_covariant_ket_apply,inner_smul_right]

theorem wick_covariant_bra_ket_conjugation (a : Parameters) (f : WickCovariantHilbert a)
    (h : 𝓢(Momentum,ℂ)) :
    wickCovariantKet a f h=star (wickCovariantBra a f h) := by
  change inner ℂ (wickCovariantNaturalTest a h) f=star (inner ℂ f (wickCovariantNaturalTest a h))
  exact (inner_conj_symm (𝕜:=ℂ) (wickCovariantNaturalTest a h) f).symm

theorem wick_covariant_bra_joint_continuous (a : Parameters) :
    Continuous (fun z : WickCovariantHilbert a × 𝓢(Momentum,ℂ) => wickCovariantBra a z.1 z.2) :=
  continuous_fst.inner ((wickCovariantNaturalTest a).continuous.comp continuous_snd)

theorem wick_covariant_ket_joint_continuous (a : Parameters) :
    Continuous (fun z : WickCovariantHilbert a × 𝓢(Momentum,ℂ) => wickCovariantKet a z.1 z.2) :=
  ((wickCovariantNaturalTest a).continuous.comp continuous_snd).inner continuous_fst

theorem wick_covariant_bra_injective (a : Parameters) : Function.Injective (wickCovariantBra a) := by
  intro f g h
  apply ext_inner_right ℂ
  have he : (fun y : WickCovariantHilbert a => inner ℂ f y)=fun y => inner ℂ g y :=
    (wick_covariant_natural_test_dense a).equalizer
      (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
      (funext (fun x => congrArg (fun B : 𝓢(Momentum,ℂ) →L[ℂ] ℂ => B x) h))
  exact congrFun he

theorem wick_covariant_ket_injective (a : Parameters) : Function.Injective (wickCovariantKet a) := by
  intro f g h
  apply wick_covariant_bra_injective a
  ext x
  have he := congrArg (fun B : 𝓢(Momentum,ℂ) →L⋆[ℂ] ℂ => star (B x)) h
  simpa only [wick_covariant_bra_ket_conjugation,star_star] using he

/-- Ordinary-dp weighted Dirac, now with the test-antilinear ket convention.
It is a generalized vector; no sharp-momentum Hilbert vector is supplied. -/
def wickCovariantMomentumKet (a : Parameters) (p : Momentum) : 𝓢(Momentum,ℂ) →L⋆[ℂ] ℂ where
  toFun h := star (wickCovariantMomentumDelta a p h)
  map_add' f g := by simp only [map_add,star_add]
  map_smul' c f := by simp only [map_smul,star_smul];rfl
  cont := continuous_star.comp (wickCovariantMomentumDelta a p).continuous

theorem wick_covariant_momentum_ket_normalization (a : Parameters) (p : Momentum)
    (h : 𝓢(Momentum,ℂ)) :
    wickCovariantMomentumKet a p (wickCovariantDensitySchwartzCLM a h)=star (h p) := by
  change star (wickCovariantMomentumDelta a p (wickCovariantDensitySchwartzCLM a h))=_
  rw [wick_covariant_momentum_delta_normalization]

end AASCKleinGordon
