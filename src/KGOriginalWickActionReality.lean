import KGOriginalWickStressHermiticity

/-! Real diagonal action and weak response of the same fixed normal-ordered
quantum tensor. No normalization or amplitude calibration is inserted. -/
noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory
open scoped SchwartzMap ComplexConjugate
open AASCSemanticExhaustion
namespace AASCKleinGordon
open SchwartzOperations

theorem original_wick_stress_metric_distribution_hermitian (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (k : WickSchwartzMetricTest) :
    star (originalWickStressMetricDistribution a s u v k)=
      originalWickStressMetricDistribution a s v u (fun i j => conjugateSchwartzCLM (k i j)) := by
  simp only [originalWickStressMetricDistribution,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,star_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact original_wick_stress_distribution_hermitian a s u v i j (k i j)

theorem original_wick_real_metric_test_diagonal_real (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (k : WickSchwartzMetricTest)
    (real : ∀ i j x,star (k i j x)=k i j x) :
    (originalWickStressMetricDistribution a s u u k).im=0 := by
  have hk : (fun i j => conjugateSchwartzCLM (k i j))=k := by
    funext i j
    ext x
    exact real i j x
  have h := original_wick_stress_metric_distribution_hermitian a s u u k
  rw [hk] at h
  have him := congrArg Complex.im h
  simp only [Complex.star_def,Complex.conj_im] at him
  linarith

theorem original_wick_quantum_action_density_hermitian (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (x : Spacetime) (G : NativeRealMatrix) :
    star (wickQuantumActionDensity G (originalWickDerivativeComponents a s u v x)
      (originalWickMassSquare a s u v x))=
      wickQuantumActionDensity G (originalWickDerivativeComponents a s v u x)
        (originalWickMassSquare a s v u x) := by
  simp [wickQuantumActionDensity,originalWickDerivativeComponents,originalWickMassSquare,
    originalDerivativeWickMatrix_hermitian,originalWickSquareMatrix_hermitian]

theorem original_wick_relative_action_hermitian (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (H : Spacetime → NativeRealMatrix) (t : ℝ) :
    star (originalWickScalarRelativeAction a s u v H t)=
      originalWickScalarRelativeAction a s v u H t := by
  unfold originalWickScalarRelativeAction
  change conj (∫ x,_) = _
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simp only [map_sub]
    exact congrArg₂ (·-·) (original_wick_quantum_action_density_hermitian a s u v x _)
      (original_wick_quantum_action_density_hermitian a s u v x _))

theorem original_wick_relative_action_diagonal_real (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (H : Spacetime → NativeRealMatrix) (t : ℝ) :
    (originalWickScalarRelativeAction a s u u H t).im=0 := by
  have h := congrArg Complex.im (original_wick_relative_action_hermitian a s u u H t)
  simp only [Complex.star_def,Complex.conj_im] at h
  linarith

theorem original_wick_raised_metric_pairing_hermitian (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (H : Spacetime → NativeRealMatrix) :
    star (originalWickRaisedMetricPairing a s u v H)=originalWickRaisedMetricPairing a s v u H := by
  unfold originalWickRaisedMetricPairing
  change conj (∫ x,_) = _
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    have hc (i j : Fin 4) : conj (originalWickScalarStressRaisedMatrix a s u v i j x)=
        originalWickScalarStressRaisedMatrix a s v u i j x :=
      original_wick_raised_stress_hermitian a s u v i j x
    simp only [map_sum,map_mul,hc,Complex.conj_ofReal])

theorem original_wick_metric_action_response_hermitian (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (H : Spacetime → NativeRealMatrix)
    (hH : Continuous H) (hcomp : HasCompactSupport H) (hsym : ∀ x i j,H x i j=H x j i) :
    star (originalWickMetricActionResponse a s u v H)=originalWickMetricActionResponse a s v u H := by
  rw [original_wick_action_response_eq_metric_pairing a s u v H hH hcomp hsym,
    original_wick_action_response_eq_metric_pairing a s v u H hH hcomp hsym]
  simp [original_wick_raised_metric_pairing_hermitian]

theorem original_wick_metric_action_response_diagonal_real (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (H : Spacetime → NativeRealMatrix)
    (hH : Continuous H) (hcomp : HasCompactSupport H) (hsym : ∀ x i j,H x i j=H x j i) :
    (originalWickMetricActionResponse a s u u H).im=0 := by
  have h := congrArg Complex.im (original_wick_metric_action_response_hermitian a s u u H hH hcomp hsym)
  simp only [Complex.star_def,Complex.conj_im] at h
  linarith

end AASCKleinGordon
