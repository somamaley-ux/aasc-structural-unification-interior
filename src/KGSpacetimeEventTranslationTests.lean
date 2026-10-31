import KGEventTranslationSchwartz
import Mathlib.MeasureTheory.Group.Integral

noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon
open SchwartzOperations

theorem spacetimeEventShift_temperate (b : Spacetime) : (fun x : Spacetime => x-b).HasTemperateGrowth :=
  (ContinuousLinearMap.id ℝ Spacetime).hasTemperateGrowth.sub (Function.HasTemperateGrowth.const b)

def spacetimeEventTranslationTestCLM (b : Spacetime) : 𝓢(Spacetime,ℂ) →L[ℂ] 𝓢(Spacetime,ℂ) :=
  SchwartzMap.compCLM ℂ (spacetimeEventShift_temperate b) (by
    refine ⟨1,1+‖b‖,fun x => ?_⟩
    rw [pow_one]
    have hb : ‖x‖ ≤ ‖x-b‖+‖b‖ := by simpa only [sub_add_cancel] using norm_add_le (x-b) b
    nlinarith [norm_nonneg (x-b),norm_nonneg b])

theorem spacetimeEventTranslationTest_apply (b : Spacetime) (h : 𝓢(Spacetime,ℂ)) (x : Spacetime) :
    spacetimeEventTranslationTestCLM b h x=h (x-b) := rfl

theorem spacetimeEventTranslationTest_zero (h : 𝓢(Spacetime,ℂ)) :
    spacetimeEventTranslationTestCLM 0 h=h := by ext x; simp [spacetimeEventTranslationTest_apply]

theorem spacetimeEventTranslationTest_add (b d : Spacetime) (h : 𝓢(Spacetime,ℂ)) :
    spacetimeEventTranslationTestCLM b (spacetimeEventTranslationTestCLM d h)=
      spacetimeEventTranslationTestCLM (b+d) h := by
  ext x
  simp only [spacetimeEventTranslationTest_apply]
  congr 1
  abel

theorem conjugate_spacetimeEventTranslationTest (b : Spacetime) (h : 𝓢(Spacetime,ℂ)) :
    conjugateSchwartzCLM (spacetimeEventTranslationTestCLM b h)=
      spacetimeEventTranslationTestCLM b (conjugateSchwartzCLM h) := by ext x; rfl

theorem fourier_spacetimeEventTranslationTest (b : Spacetime) (h : 𝓢(Spacetime,ℂ)) (q : Spacetime) :
    𝓕 (spacetimeEventTranslationTestCLM b h) q=
      Complex.exp (((-2*Real.pi*inner ℝ b q : ℝ) : ℂ)*Complex.I)*𝓕 h q := by
  rw [SchwartzMap.fourier_coe,SchwartzMap.fourier_coe,Real.fourier_eq',Real.fourier_eq']
  have he := integral_add_right_eq_self (μ := (volume : Measure Spacetime)) (fun x : Spacetime =>
    Complex.exp (((-2*Real.pi*inner ℝ x q : ℝ) : ℂ)*Complex.I)*h (x-b)) b
  change (∫ x : Spacetime, Complex.exp (((-2*Real.pi*inner ℝ x q : ℝ) : ℂ)*Complex.I)*h (x-b))=_
  rw [← he,← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [add_sub_cancel_right,inner_add_left]
    have harg : (((-2*Real.pi*(inner ℝ x q+inner ℝ b q) : ℝ) : ℂ)*Complex.I)=
        (((-2*Real.pi*inner ℝ b q : ℝ) : ℂ)*Complex.I)+
        (((-2*Real.pi*inner ℝ x q : ℝ) : ℂ)*Complex.I) := by push_cast; ring
    rw [harg,Complex.exp_add]
    simp only [smul_eq_mul]
    ring

theorem eventTranslationPhase_eq_shell_fourier_phase (a : Parameters) (b : Spacetime) (p : Momentum) :
    eventTranslationPhase a b p=
      Complex.exp (((-2*Real.pi*inner ℝ b (shellFrequency a p) : ℝ) : ℂ)*Complex.I) := by
  unfold eventTranslationPhase Translation.phase shellFrequency eventMomentumPair
  rw [inner_smul_right]
  apply congrArg (fun r : ℝ => Complex.exp ((r : ℂ)*Complex.I))
  unfold fourierWaveScale
  field_simp
  <;> ring

theorem spacetimeSmearing_eventTranslation (a : Parameters) (b : Spacetime) (h : 𝓢(Spacetime,ℂ)) :
    spacetimeSmearingCLM a (spacetimeEventTranslationTestCLM b h)=
      eventTranslationSchwartzCLM a b (spacetimeSmearingCLM a h) := by
  ext p
  rw [spacetimeSmearingCLM_apply,eventTranslationSchwartz_apply,spacetimeSmearingCLM_apply,
    fourier_spacetimeEventTranslationTest,eventTranslationPhase_eq_shell_fourier_phase]

end AASCKleinGordon
