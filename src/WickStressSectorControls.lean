import WickSchwartzSeminormBounds

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory
open scoped SchwartzMap NNReal
namespace AASCKleinGordon
open SchwartzOperations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def wickSchwartzConjugateSLM : 𝓢(E,ℂ) →ₗ⋆[ℂ] 𝓢(E,ℂ) where
  toFun := conjugateSchwartzCLM
  map_add' := conjugateSchwartz_add
  map_smul' c f := by simpa using conjugateSchwartz_smul c f

lemma wick_seminorm_conjugate_continuous (q : Seminorm ℂ 𝓢(E,ℂ)) (hq : Continuous q) :
    Continuous (q.comp wickSchwartzConjugateSLM) :=
  hq.comp conjugateSchwartzCLM.continuous

def wickStressDirectionCLM (n : ℕ) (p : ParticleConfiguration n → Spacetime) (i : Fin 4) :
    𝓢(ParticleConfiguration n,ℂ) →L[ℂ] 𝓢(ParticleConfiguration n,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (wickDirectionalCoefficient n p (spacetimeCoordinateVector i))

def wickStressMixedCLM (n : ℕ) (p q : ParticleConfiguration n → Spacetime) (i j : Fin 4) :
    𝓢(ParticleConfiguration n,ℂ) →L[ℂ] 𝓢(ParticleConfiguration n,ℂ) :=
  (wickStressDirectionCLM n q j).comp (wickStressDirectionCLM n p i)

def wickStressTraceCLM (a : Parameters) (n : ℕ) (p q : ParticleConfiguration n → Spacetime) :
    𝓢(ParticleConfiguration n,ℂ) →L[ℂ] 𝓢(ParticleConfiguration n,ℂ) :=
  -wickStressMixedCLM n p q 0 0+wickStressMixedCLM n p q 1 1+
    wickStressMixedCLM n p q 2 2+wickStressMixedCLM n p q 3 3+
    (massWaveNumber a : ℂ)^2 • ContinuousLinearMap.id ℂ _

def wickRaisedStressKernelCLM (a : Parameters) (n : ℕ) (p q : ParticleConfiguration n → Spacetime)
    (i j : Fin 4) : 𝓢(ParticleConfiguration n,ℂ) →L[ℂ] 𝓢(ParticleConfiguration n,ℂ) :=
  ((wickFlatSign i : ℂ)*(wickFlatSign j : ℂ)) •
    ((1/2 : ℂ) • (wickStressMixedCLM n p q i j+wickStressMixedCLM n p q j i)-
      ((wickFlatMetricComponent i j : ℂ)/2) • wickStressTraceCLM a n p q)

lemma wick_raised_stress_kernel_CLM_apply (a : Parameters) (n : ℕ)
    (p q : ParticleConfiguration n → Spacetime) (i j : Fin 4) (G : 𝓢(ParticleConfiguration n,ℂ)) :
    wickRaisedStressKernelCLM a n p q i j G=wickRaisedStressKernel a n p q G i j := rfl

def wickChannelKernelL1CLM (a : Parameters) (n : ℕ) (k i j : Fin 4) :
    𝓢(ParticleConfiguration (n+2),ℂ) →L[ℂ] Lp ℂ 1 (particleMeasure a (n+2)) :=
  (SchwartzMap.toLpCLM ℂ ℂ 1 (particleMeasure a (n+2))).comp
    (wickRaisedStressKernelCLM a (n+2) (wickCoreChannelFrequency0 a n k)
      (wickCoreChannelFrequency1 a n k) i j)

def wickChannelCoefficientNorm (n : ℕ) (k : Fin 4) : NNReal :=
  ⟨‖wickCoreChannelCoefficient n k‖,norm_nonneg _⟩

def wickChannelKernelL1Seminorm (a : Parameters) (n : ℕ) (k : Fin 4) :
    Seminorm ℂ 𝓢(ParticleConfiguration (n+2),ℂ) :=
  wickChannelCoefficientNorm n k •
    ∑ i : Fin 4,∑ j : Fin 4,(normSeminorm ℂ (Lp ℂ 1 (particleMeasure a (n+2)))).comp
      (wickChannelKernelL1CLM a n k i j).toLinearMap

lemma wick_channel_kernel_L1_seminorm_continuous (a : Parameters) (n : ℕ) (k : Fin 4) :
    Continuous (wickChannelKernelL1Seminorm a n k) := by
  change Continuous (fun G => wickChannelKernelL1Seminorm a n k G)
  simpa only [wickChannelKernelL1Seminorm,Seminorm.smul_apply,wick_seminorm_sum_apply,
    Seminorm.comp_apply,NNReal.smul_def,smul_eq_mul,wickChannelCoefficientNorm] using
      (continuous_finset_sum Finset.univ (fun i _ =>
        continuous_finset_sum Finset.univ (fun j _ => (wickChannelKernelL1CLM a n k i j).continuous.norm))).const_smul
          ‖wickCoreChannelCoefficient n k‖

lemma wick_channel_kernel_L1_seminorm_original (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k : Fin 4) :
    wickChannelKernelL1Seminorm a n k (wickCoreChannelStateKernel n u v k)=
      ‖wickCoreChannelCoefficient n k‖*∑ i,∑ j,wickCoreStressKernelL1 a n u v k i j := by
  simp only [wickChannelKernelL1Seminorm,Seminorm.smul_apply,wick_seminorm_sum_apply,
    Seminorm.comp_apply,NNReal.smul_def,smul_eq_mul,coe_normSeminorm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change ‖(wickRaisedStressKernel a (n+2) _ _ (wickCoreChannelStateKernel n u v k) i j).toLp 1 _‖=_
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae (((wickRaisedStressKernel a (n+2) _ _ (wickCoreChannelStateKernel n u v k) i j).coeFn_toLp 1 _).fun_comp norm)

lemma wick_aa_continuous_seminorm_control (n : ℕ)
    (q : Seminorm ℂ 𝓢(ParticleConfiguration (n+2),ℂ)) (hq : Continuous q) :
    ∃ p₁ : Seminorm ℂ 𝓢(ParticleConfiguration n,ℂ),
    ∃ p₂ : Seminorm ℂ 𝓢(ParticleConfiguration (n+2),ℂ),
      Continuous p₁ ∧ Continuous p₂ ∧ ∀ f g,q (wickAAStateKernel n f g)≤p₁ f*p₂ g := by
  let L := wickStatePullback (wickAAEmbedding n) (wickAAEmbedding_injective n)
  obtain ⟨p₁,p₂,hp₁,hp₂,hb⟩ := wick_tensor_continuous_seminorm_bound
    (q.comp L.toLinearMap) (hq.comp L.continuous)
  refine ⟨p₁.comp wickSchwartzConjugateSLM,p₂,wick_seminorm_conjugate_continuous p₁ hp₁,hp₂,?_⟩
  intro f g
  exact hb (conjugateSchwartzCLM f) g

lemma wick_mixed_continuous_seminorm_control (n : ℕ)
    (q : Seminorm ℂ 𝓢(ParticleConfiguration (n+2),ℂ)) (hq : Continuous q) :
    ∃ p₁ : Seminorm ℂ 𝓢(ParticleConfiguration (n+1),ℂ),
    ∃ p₂ : Seminorm ℂ 𝓢(ParticleConfiguration (n+1),ℂ),
      Continuous p₁ ∧ Continuous p₂ ∧ ∀ f g,q (wickMixedStateKernel n f g)≤p₁ f*p₂ g := by
  let L := wickStatePullback (wickMixedEmbedding n) (wickMixedEmbedding_injective n)
  obtain ⟨p₁,p₂,hp₁,hp₂,hb⟩ := wick_tensor_continuous_seminorm_bound
    (q.comp L.toLinearMap) (hq.comp L.continuous)
  refine ⟨p₁.comp wickSchwartzConjugateSLM,p₂,wick_seminorm_conjugate_continuous p₁ hp₁,hp₂,?_⟩
  intro f g
  exact hb (conjugateSchwartzCLM f) g

end AASCKleinGordon
