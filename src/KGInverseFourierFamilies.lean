import KGSpatialSineInitialVelocity

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform Topology
namespace AASCKleinGordon

def spatialFourierKernel (x ξ : KGSpatialSpace) : ℂ :=
  Complex.exp (((2*Real.pi*inner ℝ ξ x : ℝ) : ℂ)*Complex.I)

theorem spatialFourierKernel_norm (x ξ : KGSpatialSpace) : ‖spatialFourierKernel x ξ‖=1 := by
  simp [spatialFourierKernel,Complex.norm_exp]

theorem spatialFourierKernel_continuous (x : KGSpatialSpace) : Continuous (spatialFourierKernel x) := by
  unfold spatialFourierKernel
  fun_prop

theorem spatialFourierKernel_continuous_left (ξ : KGSpatialSpace) :
    Continuous (fun x => spatialFourierKernel x ξ) := by
  unfold spatialFourierKernel
  fun_prop

theorem spatialInverseFourier_apply (f : 𝓢(KGSpatialSpace,ℂ)) (x : KGSpatialSpace) :
    (𝓕⁻ f) x=∫ ξ, spatialFourierKernel x ξ*f ξ := by
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq']
  rfl

theorem spatialFourierKernel_mul_integrable (f : 𝓢(KGSpatialSpace,ℂ)) (x : KGSpatialSpace) :
    Integrable (fun ξ => spatialFourierKernel x ξ*f ξ) := by
  apply f.integrable.norm.mono' ((spatialFourierKernel_continuous x).mul f.continuous).aestronglyMeasurable
  exact Eventually.of_forall fun ξ => by
    simp only [Pi.mul_apply,norm_mul,spatialFourierKernel_norm,one_mul]
    exact le_rfl

/-- Derivative of an actual inverse-Fourier Schwartz family under an explicitly
integrable uniform spectral bound. No evolution or support identity is assumed. -/
theorem inverseFourierFamily_hasDerivAt
    (F G : ℝ → 𝓢(KGSpatialSpace,ℂ)) (B : KGSpatialSpace → ℝ)
    (hB : Integrable B)
    (hd : ∀ t ξ, HasDerivAt (fun s => F s ξ) (G t ξ) t)
    (hb : ∀ t ξ, ‖G t ξ‖ ≤ B ξ) (t : ℝ) (x : KGSpatialSpace) :
    HasDerivAt (fun s => (𝓕⁻ (F s)) x) ((𝓕⁻ (G t)) x) t := by
  simp_rw [spatialInverseFourier_apply]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (x₀ := t)
    (F := fun s ξ => spatialFourierKernel x ξ*F s ξ)
    (F' := fun s ξ => spatialFourierKernel x ξ*G s ξ)
    (bound := B) univ_mem
    (Eventually.of_forall fun s => (spatialFourierKernel_mul_integrable (F s) x).aestronglyMeasurable)
    (spatialFourierKernel_mul_integrable (F t) x)
    (spatialFourierKernel_mul_integrable (G t) x).aestronglyMeasurable ?_ hB ?_).2
  · exact Eventually.of_forall fun ξ s _ => by
      rw [norm_mul,spatialFourierKernel_norm,one_mul]
      exact hb s ξ
  · exact Eventually.of_forall fun ξ s _ => (hd s ξ).const_mul (spatialFourierKernel x ξ)

/-- Joint continuity follows from actual pointwise spectral continuity and a
uniform integrable bound, including the spatial oscillatory character. -/
theorem inverseFourierFamily_joint_continuous
    (F : ℝ → 𝓢(KGSpatialSpace,ℂ)) (B : KGSpatialSpace → ℝ)
    (hB : Integrable B) (hc : ∀ ξ, Continuous (fun t => F t ξ))
    (hb : ∀ t ξ, ‖F t ξ‖ ≤ B ξ) :
    Continuous (fun z : ℝ × KGSpatialSpace => (𝓕⁻ (F z.1)) z.2) := by
  simp_rw [spatialInverseFourier_apply]
  apply continuous_of_dominated
  · intro z
    exact (spatialFourierKernel_mul_integrable (F z.1) z.2).aestronglyMeasurable
  · intro z
    exact Eventually.of_forall fun ξ => by
      rw [norm_mul,spatialFourierKernel_norm,one_mul]
      exact hb z.1 ξ
  · exact hB
  · exact Eventually.of_forall fun ξ =>
      ((spatialFourierKernel_continuous_left ξ).comp continuous_snd).mul
        ((hc ξ).comp continuous_fst)

end AASCKleinGordon
