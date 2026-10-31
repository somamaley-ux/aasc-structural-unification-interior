import KGOriginalWickMetricCoefficient

/-! The same quantum tensor is a continuous functional of all sixteen
Schwartz metric-test components. State topology and Hermiticity are separate. -/
noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory
open scoped SchwartzMap BigOperators
namespace AASCKleinGordon

abbrev WickSchwartzMetricTest := Fin 4 → Fin 4 → 𝓢(Spacetime,ℂ)

def originalWickRaisedStressDistribution (a : Parameters) (s : ℝ) (u v : FiniteParticleCore)
    (i j : Fin 4) : 𝓢(Spacetime,ℂ) →L[ℂ] ℂ :=
  ((wickFlatSign i : ℂ)*(wickFlatSign j : ℂ)) • originalWickScalarStressCandidateSesqForm a s i j u v

def originalWickStressMetricDistribution (a : Parameters) (s : ℝ) (u v : FiniteParticleCore) :
    WickSchwartzMetricTest →L[ℂ] ℂ :=
  ∑ i,∑ j,(originalWickRaisedStressDistribution a s u v i j).comp
    ((ContinuousLinearMap.proj j : (Fin 4 → 𝓢(Spacetime,ℂ)) →L[ℂ] 𝓢(Spacetime,ℂ)).comp
      (ContinuousLinearMap.proj i : WickSchwartzMetricTest →L[ℂ] (Fin 4 → 𝓢(Spacetime,ℂ))))

theorem original_wick_raised_stress_test_integrable (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (i j : Fin 4) (k : 𝓢(Spacetime,ℂ)) :
    Integrable (fun x => k x*originalWickScalarStressRaisedMatrix a s u v i j x) := by
  have h0 := originalDerivativeWickMatrix_test_integrable a s u v
    (spacetimeCoordinateVector i) (spacetimeCoordinateVector j) k
  have h1 := originalDerivativeWickMatrix_test_integrable a s u v
    (spacetimeCoordinateVector j) (spacetimeCoordinateVector i) k
  have hQ := originalWickScalarLagrangianMatrix_test_integrable a s u v k
  convert (((h0.add h1).const_mul (1/2 : ℂ)).sub
    (hQ.const_mul ((wickFlatMetricComponent i j : ℂ)/2))).const_mul
      ((wickFlatSign i : ℂ)*(wickFlatSign j : ℂ)) using 1
  funext x
  simp only [originalWickScalarStressRaisedMatrix,originalWickScalarStressCandidateMatrix,
    Pi.sub_apply,Pi.add_apply]
  ring

theorem original_wick_raised_stress_distribution_pairing (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (i j : Fin 4) (k : 𝓢(Spacetime,ℂ)) :
    originalWickRaisedStressDistribution a s u v i j k =
      ∫ x,k x*originalWickScalarStressRaisedMatrix a s u v i j x := by
  simp only [originalWickRaisedStressDistribution,ContinuousLinearMap.smul_apply,smul_eq_mul,
    originalWickScalarStressCandidateSesqForm_pairing]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    unfold originalWickScalarStressRaisedMatrix
    ring)

theorem original_wick_stress_metric_distribution_pairing (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (k : WickSchwartzMetricTest) :
    originalWickStressMetricDistribution a s u v k =
      ∫ x,∑ i,∑ j,k i j x*originalWickScalarStressRaisedMatrix a s u v i j x := by
  have hi (i j : Fin 4) := original_wick_raised_stress_test_integrable a s u v i j (k i j)
  have hs (i : Fin 4) := integrable_finset_sum (Finset.univ : Finset (Fin 4)) (fun j _ => hi i j)
  rw [integral_finset_sum _ (fun i _ => hs i)]
  simp only [originalWickStressMetricDistribution,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  exact original_wick_raised_stress_distribution_pairing a s u v i j (k i j)

end AASCKleinGordon
