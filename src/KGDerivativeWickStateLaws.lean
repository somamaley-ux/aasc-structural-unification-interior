import KGDerivativeWickTestDistribution

noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

theorem originalFirstDerivativeWickBilocalCore_right_smooth (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (d0 x : Spacetime) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => originalFirstDerivativeWickBilocalCore a s u v d0 x y) := by
  unfold originalFirstDerivativeWickBilocalCore
  apply ContDiff.mul contDiff_const
  apply ContDiff.sum
  intro j hj
  exact contDiff_const.mul (wickCoreChannelFirstMatrix_right_smooth a j.1 u v j.2 d0 x)

theorem originalFirstDerivativeWickBilocalCore_fderiv_right (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (d0 d1 x y : Spacetime) :
    fderiv ℝ (fun z => originalFirstDerivativeWickBilocalCore a s u v d0 x z) y d1 =
      originalDerivativeWickBilocalCore a s u v d0 d1 x y := by
  have h := originalWickBilocalCore_mixed_fderiv a s u v x y d0 d1
  simpa only [originalWickBilocalCore_fderiv_left] using h

theorem originalFirstDerivativeWickBilocalCore_add_left (a : Parameters) (s : ℝ)
    (u u' v : FiniteParticleCore) (d0 x y : Spacetime) :
    originalFirstDerivativeWickBilocalCore a s (u+u') v d0 x y =
      originalFirstDerivativeWickBilocalCore a s u v d0 x y +
        originalFirstDerivativeWickBilocalCore a s u' v d0 x y := by
  simp_rw [← originalWickBilocalCore_fderiv_left, originalWickBilocalCore_add_left]
  rw [fderiv_fun_add
    ((originalWickBilocalCore_left_smooth a s u v y).differentiable (by simp) x)
    ((originalWickBilocalCore_left_smooth a s u' v y).differentiable (by simp) x)]
  rfl

theorem originalFirstDerivativeWickBilocalCore_add_right (a : Parameters) (s : ℝ)
    (u v v' : FiniteParticleCore) (d0 x y : Spacetime) :
    originalFirstDerivativeWickBilocalCore a s u (v+v') d0 x y =
      originalFirstDerivativeWickBilocalCore a s u v d0 x y +
        originalFirstDerivativeWickBilocalCore a s u v' d0 x y := by
  simp_rw [← originalWickBilocalCore_fderiv_left, originalWickBilocalCore_add_right]
  rw [fderiv_fun_add
    ((originalWickBilocalCore_left_smooth a s u v y).differentiable (by simp) x)
    ((originalWickBilocalCore_left_smooth a s u v' y).differentiable (by simp) x)]
  rfl

theorem originalFirstDerivativeWickBilocalCore_smul_left (a : Parameters) (s : ℝ) (c : ℂ)
    (u v : FiniteParticleCore) (d0 x y : Spacetime) :
    originalFirstDerivativeWickBilocalCore a s (c • u) v d0 x y =
      star c * originalFirstDerivativeWickBilocalCore a s u v d0 x y := by
  simp_rw [← originalWickBilocalCore_fderiv_left, originalWickBilocalCore_smul_left]
  rw [fderiv_const_mul
    ((originalWickBilocalCore_left_smooth a s u v y).differentiable (by simp) x) (star c)]
  rfl

theorem originalFirstDerivativeWickBilocalCore_smul_right (a : Parameters) (s : ℝ) (c : ℂ)
    (u v : FiniteParticleCore) (d0 x y : Spacetime) :
    originalFirstDerivativeWickBilocalCore a s u (c • v) d0 x y =
      c * originalFirstDerivativeWickBilocalCore a s u v d0 x y := by
  simp_rw [← originalWickBilocalCore_fderiv_left, originalWickBilocalCore_smul_right]
  rw [fderiv_const_mul
    ((originalWickBilocalCore_left_smooth a s u v y).differentiable (by simp) x) c]
  rfl

theorem originalDerivativeWickBilocalCore_add_left (a : Parameters) (s : ℝ)
    (u u' v : FiniteParticleCore) (d0 d1 x y : Spacetime) :
    originalDerivativeWickBilocalCore a s (u+u') v d0 d1 x y =
      originalDerivativeWickBilocalCore a s u v d0 d1 x y +
        originalDerivativeWickBilocalCore a s u' v d0 d1 x y := by
  simp_rw [← originalFirstDerivativeWickBilocalCore_fderiv_right,
    originalFirstDerivativeWickBilocalCore_add_left]
  rw [fderiv_fun_add
    ((originalFirstDerivativeWickBilocalCore_right_smooth a s u v d0 x).differentiable (by simp) y)
    ((originalFirstDerivativeWickBilocalCore_right_smooth a s u' v d0 x).differentiable (by simp) y)]
  rfl

theorem originalDerivativeWickBilocalCore_add_right (a : Parameters) (s : ℝ)
    (u v v' : FiniteParticleCore) (d0 d1 x y : Spacetime) :
    originalDerivativeWickBilocalCore a s u (v+v') d0 d1 x y =
      originalDerivativeWickBilocalCore a s u v d0 d1 x y +
        originalDerivativeWickBilocalCore a s u v' d0 d1 x y := by
  simp_rw [← originalFirstDerivativeWickBilocalCore_fderiv_right,
    originalFirstDerivativeWickBilocalCore_add_right]
  rw [fderiv_fun_add
    ((originalFirstDerivativeWickBilocalCore_right_smooth a s u v d0 x).differentiable (by simp) y)
    ((originalFirstDerivativeWickBilocalCore_right_smooth a s u v' d0 x).differentiable (by simp) y)]
  rfl

theorem originalDerivativeWickBilocalCore_smul_left (a : Parameters) (s : ℝ) (c : ℂ)
    (u v : FiniteParticleCore) (d0 d1 x y : Spacetime) :
    originalDerivativeWickBilocalCore a s (c • u) v d0 d1 x y =
      star c * originalDerivativeWickBilocalCore a s u v d0 d1 x y := by
  simp_rw [← originalFirstDerivativeWickBilocalCore_fderiv_right,
    originalFirstDerivativeWickBilocalCore_smul_left]
  rw [fderiv_const_mul
    ((originalFirstDerivativeWickBilocalCore_right_smooth a s u v d0 x).differentiable (by simp) y) (star c)]
  rfl

theorem originalDerivativeWickBilocalCore_smul_right (a : Parameters) (s : ℝ) (c : ℂ)
    (u v : FiniteParticleCore) (d0 d1 x y : Spacetime) :
    originalDerivativeWickBilocalCore a s u (c • v) d0 d1 x y =
      c * originalDerivativeWickBilocalCore a s u v d0 d1 x y := by
  simp_rw [← originalFirstDerivativeWickBilocalCore_fderiv_right,
    originalFirstDerivativeWickBilocalCore_smul_right]
  rw [fderiv_const_mul
    ((originalFirstDerivativeWickBilocalCore_right_smooth a s u v d0 x).differentiable (by simp) y) c]
  rfl

theorem originalDerivativeWickDistribution_add_left (a : Parameters) (s : ℝ)
    (u u' v : FiniteParticleCore) (d0 d1 : Spacetime) :
    originalDerivativeWickDistribution a s (u+u') v d0 d1 =
      originalDerivativeWickDistribution a s u v d0 d1 +
        originalDerivativeWickDistribution a s u' v d0 d1 := by
  ext h
  simp only [ContinuousLinearMap.add_apply, originalDerivativeWickDistribution_pairing,
    originalDerivativeWickMatrix, originalDerivativeWickBilocalCore_add_left, mul_add]
  exact integral_add (originalDerivativeWickMatrix_test_integrable a s u v d0 d1 h)
    (originalDerivativeWickMatrix_test_integrable a s u' v d0 d1 h)

theorem originalDerivativeWickDistribution_add_right (a : Parameters) (s : ℝ)
    (u v v' : FiniteParticleCore) (d0 d1 : Spacetime) :
    originalDerivativeWickDistribution a s u (v+v') d0 d1 =
      originalDerivativeWickDistribution a s u v d0 d1 +
        originalDerivativeWickDistribution a s u v' d0 d1 := by
  ext h
  simp only [ContinuousLinearMap.add_apply, originalDerivativeWickDistribution_pairing,
    originalDerivativeWickMatrix, originalDerivativeWickBilocalCore_add_right, mul_add]
  exact integral_add (originalDerivativeWickMatrix_test_integrable a s u v d0 d1 h)
    (originalDerivativeWickMatrix_test_integrable a s u v' d0 d1 h)

theorem originalDerivativeWickDistribution_smul_left (a : Parameters) (s : ℝ) (c : ℂ)
    (u v : FiniteParticleCore) (d0 d1 : Spacetime) :
    originalDerivativeWickDistribution a s (c • u) v d0 d1 =
      star c • originalDerivativeWickDistribution a s u v d0 d1 := by
  ext h
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, originalDerivativeWickDistribution_pairing,
    originalDerivativeWickMatrix, originalDerivativeWickBilocalCore_smul_left]
  simp_rw [mul_left_comm (h _) (star c)]
  exact integral_const_mul _ _

theorem originalDerivativeWickDistribution_smul_right (a : Parameters) (s : ℝ) (c : ℂ)
    (u v : FiniteParticleCore) (d0 d1 : Spacetime) :
    originalDerivativeWickDistribution a s u (c • v) d0 d1 =
      c • originalDerivativeWickDistribution a s u v d0 d1 := by
  ext h
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, originalDerivativeWickDistribution_pairing,
    originalDerivativeWickMatrix, originalDerivativeWickBilocalCore_smul_right]
  simp_rw [mul_left_comm (h _) c]
  exact integral_const_mul _ _

def originalDerivativeWickDistributionSesqForm (a : Parameters) (s : ℝ) (d0 d1 : Spacetime) :
    FiniteParticleCore →ₗ⋆[ℂ] FiniteParticleCore →ₗ[ℂ] (𝓢(Spacetime,ℂ) →L[ℂ] ℂ) where
  toFun u := {
    toFun := fun v => originalDerivativeWickDistribution a s u v d0 d1
    map_add' := fun v v' => originalDerivativeWickDistribution_add_right a s u v v' d0 d1
    map_smul' := fun c v => by
      simpa using originalDerivativeWickDistribution_smul_right a s c u v d0 d1 }
  map_add' u u' := by
    apply LinearMap.ext
    intro v
    exact originalDerivativeWickDistribution_add_left a s u u' v d0 d1
  map_smul' c u := by
    apply LinearMap.ext
    intro v
    simpa only [LinearMap.smul_apply, RCLike.star_def] using
      originalDerivativeWickDistribution_smul_left a s c u v d0 d1

end AASCKleinGordon
