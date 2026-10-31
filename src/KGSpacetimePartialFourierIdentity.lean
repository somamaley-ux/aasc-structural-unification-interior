import KGUniformSpatialFourierBounds
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

def temporalFourierKernel (freq t : ℝ) : ℂ := Complex.exp (((-2*Real.pi*freq*t : ℝ) : ℂ)*Complex.I)

theorem temporalFourierKernel_norm (freq t : ℝ) : ‖temporalFourierKernel freq t‖=1 := by
  simp [temporalFourierKernel,Complex.norm_exp]

theorem temporalFourierKernel_continuous (freq : ℝ) : Continuous (temporalFourierKernel freq) := by
  unfold temporalFourierKernel
  fun_prop

theorem spacetimeSpatialJoin_inner (t freq : ℝ) (x ξ : KGSpatialSpace) :
    inner ℝ (spacetimeSpatialJoin (t,x)) (spacetimeSpatialJoin (freq,ξ))=t*freq+inner ℝ x ξ := by
  simp [PiLp.inner_apply,Fin.sum_univ_succ,spacetimeSpatialJoin_zero,spacetimeSpatialJoin_succ,mul_comm]

theorem spacetimeFourierKernel_split (t freq : ℝ) (x ξ : KGSpatialSpace) :
    Complex.exp (((-2*Real.pi*inner ℝ (spacetimeSpatialJoin (t,x)) (spacetimeSpatialJoin (freq,ξ)) : ℝ) : ℂ)*Complex.I)=
      temporalFourierKernel freq t*spatialFourierKernel (-ξ) x := by
  rw [spacetimeSpatialJoin_inner]
  unfold temporalFourierKernel spatialFourierKernel
  rw [← Complex.exp_add]
  congr 1
  simp only [inner_neg_right]
  push_cast
  ring

/-- Exact partial-Fourier identity, with tau=x0 and the original spacetime volume.
Fubini here is only over tau and x at each fixed frequency. -/
theorem spacetimeFourier_eq_time_spatialFourier (h : 𝓢(Spacetime,ℂ)) (freq : ℝ) (ξ : KGSpatialSpace) :
    𝓕 h (spacetimeSpatialJoin (freq,ξ))=
      ∫ t : ℝ, temporalFourierKernel freq t*𝓕 (spacetimeSpatialSliceCLM t h) ξ := by
  let G := fun z : ℝ × KGSpatialSpace =>
    (temporalFourierKernel freq z.1*spatialFourierKernel (-ξ) z.2)*h (spacetimeSpatialJoin z)
  have hi : Integrable (fun z : ℝ × KGSpatialSpace => h (spacetimeSpatialJoin z)) :=
    spacetimeSpatialJoin_preserves_volume.integrable_comp_of_integrable h.integrable
  have hg : Integrable G := by
    apply hi.norm.mono' ?_ (Eventually.of_forall fun z => by
      simp only [G,norm_mul,temporalFourierKernel_norm,spatialFourierKernel_norm,one_mul,le_refl])
    exact (((temporalFourierKernel_continuous freq).comp continuous_fst).mul
      ((spatialFourierKernel_continuous (-ξ)).comp continuous_snd)).mul
        (h.continuous.comp spacetimeSpatialJoin.continuous) |>.aestronglyMeasurable
  calc
    _ = ∫ z : ℝ × KGSpatialSpace, G z := by
      rw [SchwartzMap.fourier_coe,Real.fourier_eq',spacetimeSpatialJoin_integral]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp only
        rw [spacetimeFourierKernel_split]
        rfl
    _ = ∫ t : ℝ, ∫ x : KGSpatialSpace, G (t,x) := integral_prod G hg
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        dsimp only
        rw [spatialFourier_apply,← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          dsimp only [G]
          rw [spacetimeSpatialSlice_apply]
          ring

end AASCKleinGordon
