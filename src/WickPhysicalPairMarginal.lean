import WickCoordinatePartialIntegral
import KGParticleProductTransport

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

def wickConfigurationEuclidean (n : ℕ) : ParticleConfiguration n ≃L[ℝ]
    EuclideanSpace ℝ (Fin n × Fin 3) :=
  ({ toFun x := WithLp.toLp 2 (fun i : Fin n × Fin 3 => x i.1 i.2)
     invFun y i j := y (i,j)
     map_add' _ _ := rfl
     map_smul' _ _ := rfl
     left_inv _ := rfl
     right_inv y := by ext i; rfl } :
      ParticleConfiguration n ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin 3)).toContinuousLinearEquiv

def wickJoinVisiblePair (n : ℕ) :
    (ParticleConfiguration n × (Momentum × Momentum)) ≃L[ℝ] ParticleConfiguration (n+2) :=
  ({ toFun z := Fin.cons z.2.1 (Fin.cons z.2.2 z.1)
     invFun z := (Fin.tail (Fin.tail z),(z 0,z 1))
     map_add' z w := by
       ext i
       cases i using Fin.cases with
       | zero => rfl
       | succ i => cases i using Fin.cases <;> rfl
     map_smul' c z := by
       ext i
       cases i using Fin.cases with
       | zero => rfl
       | succ i => cases i using Fin.cases <;> rfl
     left_inv z := by
       rcases z with ⟨r,p,q⟩
       rfl
     right_inv z := by
       ext i
       cases i using Fin.cases with
       | zero => rfl
       | succ i => cases i using Fin.cases <;> rfl } :
    (ParticleConfiguration n × (Momentum × Momentum)) ≃ₗ[ℝ]
      ParticleConfiguration (n+2)).toContinuousLinearEquiv

def wickPhysicalPairMarginalCLM (a : Parameters) (n : ℕ) :
    𝓢(ParticleConfiguration (n+2),ℂ) →L[ℂ] 𝓢(Momentum × Momentum,ℂ) :=
  (wickCoordinatePartialIntegralCLM (particleMeasure a n) (wickConfigurationEuclidean n)).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (wickJoinVisiblePair n))

theorem wick_physical_pair_marginal_apply (a : Parameters) (n : ℕ)
    (G : 𝓢(ParticleConfiguration (n+2),ℂ)) (p q : Momentum) :
    wickPhysicalPairMarginalCLM a n G (p,q)=
      ∫ r,G (Fin.cons p (Fin.cons q r)) ∂particleMeasure a n := by
  rw [wickPhysicalPairMarginalCLM,ContinuousLinearMap.comp_apply,wick_coordinate_partial_integral_apply]
  rfl

def wickOriginalStressPairMarginal (a : Parameters) (n : ℕ) (u v : FiniteParticleCore)
    (k : Fin 4) (j : Fin 4) : 𝓢(Momentum × Momentum,ℂ) :=
  wickPhysicalPairMarginalCLM a n
    (wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n k)
      (wickCoreChannelFrequency1 a n k) (wickCoreChannelStateKernel n u v k) 0 j)

theorem wick_original_stress_pair_marginal_apply (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k j : Fin 4) (p q : Momentum) :
    wickOriginalStressPairMarginal a n u v k j (p,q)=
      ∫ r,wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n k)
        (wickCoreChannelFrequency1 a n k) (wickCoreChannelStateKernel n u v k) 0 j
        (Fin.cons p (Fin.cons q r)) ∂particleMeasure a n :=
  wick_physical_pair_marginal_apply a n _ p q

end AASCKleinGordon
