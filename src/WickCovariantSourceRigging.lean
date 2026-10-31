import WickCovariantBraKet
import WickOriginalCoreControls
import WickJointContinuityCriterion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

theorem wick_covariant_original_core_apply (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    wickCovariantOriginalCore a f=wickOneParticleCore (wickCovariantOriginalSector a f) := rfl

/- Prevent elaborator comparison from expanding the entire original source
construction or the core map. Their values remain available by explicit lemmas. -/
attribute [local irreducible] originalWickRaisedStressDistribution wickCovariantOriginalCore

/-- The SAME attached source, with real-linear test slot only to use the
proved three-variable continuity criterion. Complex test linearity is retained
by originalWickRaisedStressDistribution itself. -/
def wickOriginalRaisedStressSesqReal (a : Parameters) (s : ℝ) (i j : Fin 4) :
    FiniteParticleCore →ₗ⋆[ℂ] FiniteParticleCore →ₗ[ℂ] (𝓢(Spacetime,ℂ) →L[ℝ] ℂ) where
  toFun u :=
    { toFun v := (originalWickRaisedStressDistribution a s u v i j).restrictScalars ℝ
      map_add' v w := by
        ext h
        simp [originalWickRaisedStressDistribution,map_add]
      map_smul' c v := by
        ext h
        simp [originalWickRaisedStressDistribution,map_smul]
        ring }
  map_add' u v := by
    apply LinearMap.ext
    intro w
    apply ContinuousLinearMap.ext
    intro h
    simp [originalWickRaisedStressDistribution,map_add]
  map_smul' c u := by
    apply LinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro h
    simp [originalWickRaisedStressDistribution]
    ring

theorem wick_original_raised_stress_continuous_bound (a : Parameters) (s : ℝ)
    (i j : Fin 4) (u v : FiniteParticleCore) (h : 𝓢(Spacetime,ℂ)) :
    ‖originalWickRaisedStressDistribution a s u v i j h‖≤
      wickOriginalLeftCoreSeminorm a s u*wickOriginalRightCoreSeminorm a v*
        ‖h.toLp 1 volume‖ := by
  rw [wick_schwartz_L1_norm]
  exact (original_wick_distribution_common_L1_bound a s u v i j h).trans
    (mul_le_mul_of_nonneg_right
      ((original_wick_stress_entry_le_total_state_bound a s u v i j).trans
        (original_wick_total_state_bound_continuous_controls a s u v))
      (integral_nonneg (fun _ => norm_nonneg _)))

theorem wick_original_raised_stress_joint_continuous (a : Parameters) (s : ℝ) (i j : Fin 4) :
    Continuous (fun z : (FiniteParticleCore × FiniteParticleCore) × 𝓢(Spacetime,ℂ) =>
      originalWickRaisedStressDistribution a s z.1.1 z.1.2 i j z.2) := by
  apply wick_joint_sesq_test_continuous (wickOriginalRaisedStressSesqReal a s i j)
    (wickOriginalLeftCoreSeminorm a s) (wickOriginalRightCoreSeminorm a)
    (fun h => ‖h.toLp 1 volume‖)
    (wick_original_left_core_seminorm_continuous a s)
    (wick_original_right_core_seminorm_continuous a)
    (SchwartzMap.toLpCLM ℝ ℂ 1 (volume : Measure Spacetime)).continuous.norm
  · change ‖(SchwartzMap.toLpCLM ℝ ℂ 1 (volume : Measure Spacetime)) 0‖=0
    rw [map_zero,norm_zero]
  · exact wick_original_raised_stress_continuous_bound a s i j

def wickCovariantSourceForm (a : Parameters) (s : ℝ) (i j : Fin 4)
    (f g : 𝓢(Momentum,ℂ)) : 𝓢(Spacetime,ℂ) →L[ℂ] ℂ :=
  originalWickRaisedStressDistribution a s
    (wickCovariantOriginalCore a f) (wickCovariantOriginalCore a g) i j

theorem wick_covariant_source_joint_continuous (a : Parameters) (s : ℝ) (i j : Fin 4) :
    Continuous (fun z : (𝓢(Momentum,ℂ) × 𝓢(Momentum,ℂ)) × 𝓢(Spacetime,ℂ) =>
      wickCovariantSourceForm a s i j z.1.1 z.1.2 z.2) := by
  have ht : Continuous (fun z : (𝓢(Momentum,ℂ) × 𝓢(Momentum,ℂ)) × 𝓢(Spacetime,ℂ) =>
      ((wickCovariantOriginalCore a z.1.1,wickCovariantOriginalCore a z.1.2),z.2)) := by
    fun_prop
  simpa only [Function.comp_def,wickCovariantSourceForm] using
    (wick_original_raised_stress_joint_continuous a s i j).comp ht

/-- A continuous antidual in the first state variable, linear in the ket
variable. Its value is the original full stress, not the half action response. -/
def wickCovariantSourceAntidual (a : Parameters) (s : ℝ) (i j : Fin 4)
    (h : 𝓢(Spacetime,ℂ)) (g : 𝓢(Momentum,ℂ)) : 𝓢(Momentum,ℂ) →L⋆[ℂ] ℂ where
  toFun f := wickCovariantSourceForm a s i j f g h
  map_add' f k := by
    change wickOriginalRaisedStressSesqReal a s i j (wickCovariantOriginalCore a (f+k))
      (wickCovariantOriginalCore a g) h=_
    simp only [map_add,LinearMap.add_apply,ContinuousLinearMap.add_apply]
    rfl
  map_smul' c f := by
    change wickOriginalRaisedStressSesqReal a s i j (wickCovariantOriginalCore a (c • f))
      (wickCovariantOriginalCore a g) h=_
    rw [map_smul,map_smulₛₗ]
    simp only [LinearMap.smul_apply,ContinuousLinearMap.smul_apply]
    rfl
  cont := by
    have ht : Continuous (fun f : 𝓢(Momentum,ℂ) => ((f,g),h)) :=
      (continuous_id.prodMk continuous_const).prodMk continuous_const
    simpa only [Function.comp_def] using (wick_covariant_source_joint_continuous a s i j).comp ht

def wickCovariantSourceOperatorLM (a : Parameters) (s : ℝ) (i j : Fin 4)
    (h : 𝓢(Spacetime,ℂ)) :
    𝓢(Momentum,ℂ) →ₗ[ℂ] (𝓢(Momentum,ℂ) →L⋆[ℂ] ℂ) where
  toFun g := wickCovariantSourceAntidual a s i j h g
  map_add' f g := by
    ext k
    change wickOriginalRaisedStressSesqReal a s i j (wickCovariantOriginalCore a k)
      (wickCovariantOriginalCore a (f+g)) h=_
    simp only [map_add,ContinuousLinearMap.add_apply]
    rfl
  map_smul' c g := by
    ext k
    change wickOriginalRaisedStressSesqReal a s i j (wickCovariantOriginalCore a k)
      (wickCovariantOriginalCore a (c • g)) h=_
    simp only [map_smul,ContinuousLinearMap.smul_apply]
    rfl

theorem wick_covariant_rigged_source_square (a : Parameters) (s : ℝ) (i j : Fin 4)
    (f g : 𝓢(Momentum,ℂ)) (h : 𝓢(Spacetime,ℂ)) :
    wickCovariantSourceOperatorLM a s i j h g f=
      ∫ p,∫ q,(𝓕 h) (shellFrequency a p-shellFrequency a q)*wickCovariantTensorKernel a s p q i j*
        star (f p)*g q ∂wickCovariantMeasure a ∂wickCovariantMeasure a := by
  change originalWickRaisedStressDistribution a s
    (wickCovariantOriginalCore a f) (wickCovariantOriginalCore a g) i j h=_
  rw [wick_covariant_original_core_apply,wick_covariant_original_core_apply]
  rw [wick_original_covariant_source_test_incidence,
    wick_covariant_original_sector_wavefunction,wick_covariant_original_sector_wavefunction]

theorem wick_covariant_calibrated_rigged_source_square (a : Parameters) (i j : Fin 4)
    (f g : 𝓢(Momentum,ℂ)) (h : 𝓢(Spacetime,ℂ)) :
    wickCovariantSourceOperatorLM a (wickPositiveCalibratedAmplitude a) i j h g f=
      ∫ p,∫ q,(𝓕 h) (shellFrequency a p-shellFrequency a q)*
        ((a.speed : ℂ)*(scalarMatrixElement a (massShell a p) (massShell a q) i j : ℂ))*
          star (f p)*g q ∂wickCovariantMeasure a ∂wickCovariantMeasure a := by
  rw [wick_covariant_rigged_source_square]
  simp_rw [wick_covariant_calibrated_tensor_kernel]

/-- Uniqueness on the full natural state-test rigging follows from exact
surjective reparameterization of the SAME original core. This is not a
Schwartz product-test density theorem for arbitrary two-momentum distributions. -/
theorem wick_covariant_same_source_form_unique (a : Parameters) (s : ℝ) (i j : Fin 4)
    (B : 𝓢(Momentum,ℂ) → 𝓢(Momentum,ℂ) → 𝓢(Spacetime,ℂ) → ℂ)
    (hB : ∀ f g : bosonicSchwartz 1,∀ h,
      B (wickCovariantSchwartz a (sectorOneToSchwartz f))
        (wickCovariantSchwartz a (sectorOneToSchwartz g)) h=
      originalWickRaisedStressDistribution a s (wickOneParticleCore f) (wickOneParticleCore g) i j h)
    (f g : 𝓢(Momentum,ℂ)) (h : 𝓢(Spacetime,ℂ)) :
    B f g h=wickCovariantSourceForm a s i j f g h := by
  have he := hB (wickCovariantOriginalSector a f) (wickCovariantOriginalSector a g) h
  rw [wick_covariant_original_sector_wavefunction,wick_covariant_original_sector_wavefunction] at he
  rw [← wick_covariant_original_core_apply,← wick_covariant_original_core_apply] at he
  exact he

end AASCKleinGordon
