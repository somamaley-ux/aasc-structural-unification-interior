import KGOriginalWickWeakConservation

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory
open scoped SchwartzMap BigOperators
namespace AASCKleinGordon

theorem original_wick_raised_stress_distribution_symmetric (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (i j : Fin 4) :
    originalWickRaisedStressDistribution a s u v i j=originalWickRaisedStressDistribution a s u v j i := by
  ext h
  rw [original_wick_raised_stress_distribution_pairing,original_wick_raised_stress_distribution_pairing]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    unfold originalWickScalarStressRaisedMatrix
    dsimp only
    rw [originalWickScalarStressCandidateMatrix_symmetric a s u v i j x]
    ring)

def wickFlatLieMetricTest (X : Fin 4 → 𝓢(Spacetime,ℂ)) : WickSchwartzMetricTest :=
  fun i j => (wickFlatSign j : ℂ) • wickDirectionalTestCLM (spacetimeCoordinateVector i) (X j)+
    (wickFlatSign i : ℂ) • wickDirectionalTestCLM (spacetimeCoordinateVector j) (X i)

theorem wick_flat_lie_metric_test_apply (X : Fin 4 → 𝓢(Spacetime,ℂ)) (i j : Fin 4) (x : Spacetime) :
    wickFlatLieMetricTest X i j x=(wickFlatSign j : ℂ)*fderiv ℝ (X j) x (spacetimeCoordinateVector i)+
      (wickFlatSign i : ℂ)*fderiv ℝ (X i) x (spacetimeCoordinateVector j) := rfl

theorem original_wick_flat_lie_test_ward (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (X : Fin 4 → 𝓢(Spacetime,ℂ)) :
    originalWickStressMetricDistribution a s u v (wickFlatLieMetricTest X)=0 := by
  have hA : (∑ i,∑ j,(wickFlatSign j : ℂ)*originalWickRaisedStressDistribution a s u v i j
      (wickDirectionalTestCLM (spacetimeCoordinateVector i) (X j)))=0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j hj
    rw [← Finset.mul_sum,original_wick_stress_distribution_conserved,mul_zero]
  have hB : (∑ i,∑ j,(wickFlatSign i : ℂ)*originalWickRaisedStressDistribution a s u v i j
      (wickDirectionalTestCLM (spacetimeCoordinateVector j) (X i)))=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [← Finset.mul_sum]
    have hs : (∑ j,originalWickRaisedStressDistribution a s u v i j
        (wickDirectionalTestCLM (spacetimeCoordinateVector j) (X i)))=
        ∑ j,originalWickRaisedStressDistribution a s u v j i
          (wickDirectionalTestCLM (spacetimeCoordinateVector j) (X i)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [original_wick_raised_stress_distribution_symmetric a s u v i j]
    rw [hs,original_wick_stress_distribution_conserved,mul_zero]
  simp only [originalWickStressMetricDistribution,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,wickFlatLieMetricTest,
    map_add,map_smul,smul_eq_mul]
  simp_rw [Finset.sum_add_distrib]
  rw [hA,hB,add_zero]

theorem original_wick_action_ward_on_represented_lie_test (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (H : Spacetime → AASCSemanticExhaustion.NativeRealMatrix)
    (hH : Continuous H) (hcomp : HasCompactSupport H) (hsym : ∀ x i j,H x i j=H x j i)
    (X : Fin 4 → 𝓢(Spacetime,ℂ)) (hLie : ∀ x i j,(H x i j : ℂ)=wickFlatLieMetricTest X i j x) :
    HasDerivAt (originalWickScalarRelativeAction a s u v H) 0 0 := by
  have hd := original_wick_action_derivative_eq_test_distribution a s u v H hH hcomp hsym
    (wickFlatLieMetricTest X) hLie
  simpa only [original_wick_flat_lie_test_ward,mul_zero] using hd

end AASCKleinGordon
