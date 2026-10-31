import KGOriginalWickSesquilinearity

noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

theorem originalWickSquareMatrix_add_left (a : Parameters) (s : ℝ)
    (u u' v : FiniteParticleCore) (x : Spacetime) :
    originalWickSquareMatrix a s (u+u') v x =
      originalWickSquareMatrix a s u v x + originalWickSquareMatrix a s u' v x :=
  originalWickBilocalCore_add_left a s u u' v x x

theorem originalWickSquareMatrix_add_right (a : Parameters) (s : ℝ)
    (u v v' : FiniteParticleCore) (x : Spacetime) :
    originalWickSquareMatrix a s u (v+v') x =
      originalWickSquareMatrix a s u v x + originalWickSquareMatrix a s u v' x :=
  originalWickBilocalCore_add_right a s u v v' x x

theorem originalWickSquareMatrix_smul_left (a : Parameters) (s : ℝ) (c : ℂ)
    (u v : FiniteParticleCore) (x : Spacetime) :
    originalWickSquareMatrix a s (c • u) v x = star c * originalWickSquareMatrix a s u v x :=
  originalWickBilocalCore_smul_left a s c u v x x

theorem originalWickSquareMatrix_smul_right (a : Parameters) (s : ℝ) (c : ℂ)
    (u v : FiniteParticleCore) (x : Spacetime) :
    originalWickSquareMatrix a s u (c • v) x = c * originalWickSquareMatrix a s u v x :=
  originalWickBilocalCore_smul_right a s c u v x x

theorem originalWickSquareMatrix_test_integrable (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (h : 𝓢(Spacetime,ℂ)) :
    Integrable (fun x => h x * originalWickSquareMatrix a s u v x) := by
  let S := (Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4))
  have hi : ∀ j∈S, Integrable (fun x => wickCoreChannelCoefficient j.1 j.2 *
      (h x * wickCoreChannelMatrix a j.1 u v j.2 x x)) := by
    intro j hj
    apply Integrable.const_mul
    simp_rw [wickCoreChannelMatrix_diagonal]
    exact wickLocalMatrix_test_integrable a (j.1+2) _
      (((wickCoreChannelFrequency0_temperate a j.1 j.2).add
        (wickCoreChannelFrequency1_temperate a j.1 j.2)).1.continuous) _ h
  have hh := (integrable_finset_sum S hi).const_mul ((s : ℂ)^2)
  convert hh using 1
  funext x
  change h x * ((s : ℂ)^2 * ∑ j∈S,wickCoreChannelCoefficient j.1 j.2 *
    wickCoreChannelMatrix a j.1 u v j.2 x x) = _
  calc
    _ = (s : ℂ)^2 * (h x * ∑ j∈S,wickCoreChannelCoefficient j.1 j.2 *
      wickCoreChannelMatrix a j.1 u v j.2 x x) := by ring
    _ = _ := by
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem originalWickSquareDistribution_add_left (a : Parameters) (s : ℝ)
    (u u' v : FiniteParticleCore) :
    originalWickSquareDistribution a s (u+u') v =
      originalWickSquareDistribution a s u v + originalWickSquareDistribution a s u' v := by
  ext h
  simp only [ContinuousLinearMap.add_apply, originalWickSquareDistribution_pairing,
    originalWickSquareMatrix_add_left, mul_add]
  exact integral_add (originalWickSquareMatrix_test_integrable a s u v h)
    (originalWickSquareMatrix_test_integrable a s u' v h)

theorem originalWickSquareDistribution_add_right (a : Parameters) (s : ℝ)
    (u v v' : FiniteParticleCore) :
    originalWickSquareDistribution a s u (v+v') =
      originalWickSquareDistribution a s u v + originalWickSquareDistribution a s u v' := by
  ext h
  simp only [ContinuousLinearMap.add_apply, originalWickSquareDistribution_pairing,
    originalWickSquareMatrix_add_right, mul_add]
  exact integral_add (originalWickSquareMatrix_test_integrable a s u v h)
    (originalWickSquareMatrix_test_integrable a s u v' h)

theorem originalWickSquareDistribution_smul_left (a : Parameters) (s : ℝ) (c : ℂ)
    (u v : FiniteParticleCore) :
    originalWickSquareDistribution a s (c • u) v = star c • originalWickSquareDistribution a s u v := by
  ext h
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
    originalWickSquareDistribution_pairing, originalWickSquareMatrix_smul_left]
  simp_rw [mul_left_comm (h _) (star c)]
  exact integral_const_mul _ _

theorem originalWickSquareDistribution_smul_right (a : Parameters) (s : ℝ) (c : ℂ)
    (u v : FiniteParticleCore) :
    originalWickSquareDistribution a s u (c • v) = c • originalWickSquareDistribution a s u v := by
  ext h
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
    originalWickSquareDistribution_pairing, originalWickSquareMatrix_smul_right]
  simp_rw [mul_left_comm (h _) c]
  exact integral_const_mul _ _

/-- A distribution-valued sesquilinear form on the SAME original algebraic core.
Each state matrix is a continuous Schwartz test functional. This does not
assert continuity in a separately chosen topology on the original core. -/
def originalWickSquareDistributionSesqForm (a : Parameters) (s : ℝ) :
    FiniteParticleCore →ₗ⋆[ℂ] FiniteParticleCore →ₗ[ℂ] (𝓢(Spacetime,ℂ) →L[ℂ] ℂ) where
  toFun u := {
    toFun := originalWickSquareDistribution a s u
    map_add' := originalWickSquareDistribution_add_right a s u
    map_smul' := fun c v => by
      simpa using originalWickSquareDistribution_smul_right a s c u v }
  map_add' u u' := by
    apply LinearMap.ext
    intro v
    exact originalWickSquareDistribution_add_left a s u u' v
  map_smul' c u := by
    apply LinearMap.ext
    intro v
    simpa only [LinearMap.smul_apply, RCLike.star_def] using
      originalWickSquareDistribution_smul_left a s c u v

theorem originalWickSquareDistributionSesqForm_pairing (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (h : 𝓢(Spacetime,ℂ)) :
    originalWickSquareDistributionSesqForm a s u v h =
      ∫ x,h x * originalWickSquareMatrix a s u v x :=
  originalWickSquareDistribution_pairing a s u v h

end AASCKleinGordon
