import KGWickStateKernelLaws

noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
attribute [local instance 101] secondCountableTopologyEither_of_left
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

def wickDirectionalCoefficient (n : ℕ) (ω : ParticleConfiguration n → Spacetime)
    (d : Spacetime) (z : ParticleConfiguration n) : ℂ :=
  -(2 * Real.pi * Complex.I) * (inner ℝ d (ω z) : ℂ)

theorem wickDirectionalCoefficient_temperate (n : ℕ) (ω : ParticleConfiguration n → Spacetime)
    (hω : ω.HasTemperateGrowth) (d : Spacetime) :
    (wickDirectionalCoefficient n ω d).HasTemperateGrowth :=
  (Function.HasTemperateGrowth.const _).mul
    (Complex.ofRealCLM.hasTemperateGrowth.comp ((innerSL ℝ d).hasTemperateGrowth.comp hω))

def wickDirectionalStateKernel (n : ℕ) (ω : ParticleConfiguration n → Spacetime)
    (d : Spacetime) (G : 𝓢(ParticleConfiguration n,ℂ)) : 𝓢(ParticleConfiguration n,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (wickDirectionalCoefficient n ω d) G

@[simp] theorem wickDirectionalStateKernel_apply (n : ℕ) (ω : ParticleConfiguration n → Spacetime)
    (hω : ω.HasTemperateGrowth) (d : Spacetime) (G : 𝓢(ParticleConfiguration n,ℂ))
    (z : ParticleConfiguration n) :
    wickDirectionalStateKernel n ω d G z = wickDirectionalCoefficient n ω d z * G z :=
  SchwartzMap.smulLeftCLM_apply_apply (wickDirectionalCoefficient_temperate n ω hω d) G z

/-- A derivative of the local Fourier matrix is a frequency multiplier on the
actual Schwartz state kernel. All moment/integral hypotheses are proved. -/
theorem wickLocalMatrix_directional_fderiv (a : Parameters) (n : ℕ)
    (ω : ParticleConfiguration n → Spacetime) (hω : ω.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (x d : Spacetime) :
    fderiv ℝ (wickLocalMatrix a n ω G) x d =
      wickLocalMatrix a n ω (wickDirectionalStateKernel n ω d G) x := by
  have hG : Integrable (fun t : Spacetime × ParticleConfiguration n => G t.2)
      (Measure.map (wickFrequencyGraph n ω) (particleMeasure a n)) :=
    (integrable_map_measure (G.continuous.comp continuous_snd).aestronglyMeasurable
      (show AEMeasurable (wickFrequencyGraph n ω) (particleMeasure a n) from
        (hω.1.continuous.prodMk continuous_id).aemeasurable)).mpr G.integrable
  have hm : Integrable (fun t : Spacetime × ParticleConfiguration n => ‖t‖ * ‖G t.2‖)
      (Measure.map (wickFrequencyGraph n ω) (particleMeasure a n)) := by
    simpa only [pow_one] using wick_graph_measure_moments a n 1 ω hω G
  have hd : Integrable (fun t : Spacetime × ParticleConfiguration n =>
      Real.fourierChar (-(wickGraphPairing n) t x) •
        VectorFourier.fourierSMulRight (wickGraphPairing n) (fun t => G t.2) t)
      (Measure.map (wickFrequencyGraph n ω) (particleMeasure a n)) := by
    apply (hm.const_mul (2 * Real.pi * ‖wickGraphPairing n‖)).mono
    · exact (Real.continuous_fourierChar.comp
        (((wickGraphPairing n).flip x).continuous.neg)).aestronglyMeasurable.smul
        hG.aestronglyMeasurable.fourierSMulRight
    · exact ae_of_all _ fun t => by
        change ‖(Real.fourierChar (-(wickGraphPairing n) t x) : ℂ) •
          VectorFourier.fourierSMulRight (wickGraphPairing n) (fun t => G t.2) t‖ ≤ _
        rw [norm_smul, Circle.norm_coe, one_mul, Real.norm_of_nonneg (by positivity)]
        simpa only [mul_assoc] using
          VectorFourier.norm_fourierSMulRight_le (wickGraphPairing n) (fun t => G t.2) t
  rw [wickLocalMatrix_eq_graph_fourier a n ω hω.1.continuous G]
  rw [VectorFourier.fderiv_fourierIntegral (wickGraphPairing n) hG hm]
  rw [VectorFourier.fourierIntegral]
  change (∫ t : Spacetime × ParticleConfiguration n,
    Real.fourierChar (-(wickGraphPairing n) t x) •
      VectorFourier.fourierSMulRight (wickGraphPairing n) (fun t => G t.2) t
        ∂Measure.map (wickFrequencyGraph n ω) (particleMeasure a n)) d = _
  rw [ContinuousLinearMap.integral_apply hd]
  have hmeas : AEStronglyMeasurable (fun t : Spacetime × ParticleConfiguration n =>
      (Real.fourierChar (-(wickGraphPairing n) t x) •
        VectorFourier.fourierSMulRight (wickGraphPairing n) (fun t => G t.2) t) d)
      (Measure.map (wickFrequencyGraph n ω) (particleMeasure a n)) :=
    (ContinuousLinearMap.apply ℝ ℂ d).continuous.comp_aestronglyMeasurable hd.aestronglyMeasurable
  rw [integral_map
    (show AEMeasurable (wickFrequencyGraph n ω) (particleMeasure a n) from
      (hω.1.continuous.prodMk continuous_id).aemeasurable)
    hmeas]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
      simp only [ContinuousLinearMap.smul_apply, VectorFourier.fourierSMulRight_apply,
        wickDirectionalStateKernel_apply n ω hω,
        Circle.smul_def, smul_eq_mul, Complex.real_smul, wickDirectionalCoefficient, mul_assoc]
      change (Real.fourierChar (-inner ℝ (ω z) x) : ℂ) *
        (-(2 * (Real.pi * Complex.I)) * (((inner ℝ (ω z) d : ℝ) : ℂ) * G z)) =
        (Real.fourierChar (-inner ℝ x (ω z)) : ℂ) *
        (-(2 * (Real.pi * Complex.I)) * (((inner ℝ d (ω z) : ℝ) : ℂ) * G z))
      rw [real_inner_comm (ω z) x, real_inner_comm (ω z) d]

theorem wickBilocalMatrix_fderiv_left (a : Parameters) (n : ℕ)
    (ω0 ω1 : ParticleConfiguration n → Spacetime)
    (h0 : ω0.HasTemperateGrowth) (h1 : ω1.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (x y d : Spacetime) :
    fderiv ℝ (fun x => wickBilocalMatrix a n ω0 ω1 G x y) x d =
      wickBilocalMatrix a n ω0 ω1 (wickDirectionalStateKernel n ω0 d G) x y := by
  change fderiv ℝ (wickLocalMatrix a n ω0 (wickPhaseStateKernel n ω1 G y)) x d = _
  rw [wickLocalMatrix_directional_fderiv a n ω0 h0]
  unfold wickBilocalMatrix
  congr 1
  apply SchwartzMap.ext
  intro z
  simp only [wickDirectionalStateKernel_apply n ω0 h0,
    wickPhaseStateKernel_apply n ω1 h1, Circle.smul_def, smul_eq_mul]
  ring

theorem wickBilocalMatrix_fderiv_right (a : Parameters) (n : ℕ)
    (ω0 ω1 : ParticleConfiguration n → Spacetime)
    (h0 : ω0.HasTemperateGrowth) (h1 : ω1.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (x y d : Spacetime) :
    fderiv ℝ (fun y => wickBilocalMatrix a n ω0 ω1 G x y) y d =
      wickBilocalMatrix a n ω0 ω1 (wickDirectionalStateKernel n ω1 d G) x y := by
  simp_rw [wickBilocalMatrix_swap a n ω0 ω1 h0 h1]
  rw [wickBilocalMatrix_fderiv_left a n ω1 ω0 h1 h0]

/-- Two different field factors are differentiated before coincidence. -/
theorem wickBilocalMatrix_mixed_fderiv (a : Parameters) (n : ℕ)
    (ω0 ω1 : ParticleConfiguration n → Spacetime)
    (h0 : ω0.HasTemperateGrowth) (h1 : ω1.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (x y d0 d1 : Spacetime) :
    fderiv ℝ (fun y => fderiv ℝ (fun x => wickBilocalMatrix a n ω0 ω1 G x y) x d0) y d1 =
      wickBilocalMatrix a n ω0 ω1
        (wickDirectionalStateKernel n ω1 d1 (wickDirectionalStateKernel n ω0 d0 G)) x y := by
  simp_rw [wickBilocalMatrix_fderiv_left a n ω0 ω1 h0 h1]
  exact wickBilocalMatrix_fderiv_right a n ω0 ω1 h0 h1 _ x y d1

theorem wickBilocalMatrix_mixed_fderiv_diagonal (a : Parameters) (n : ℕ)
    (ω0 ω1 : ParticleConfiguration n → Spacetime)
    (h0 : ω0.HasTemperateGrowth) (h1 : ω1.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (x d0 d1 : Spacetime) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => wickBilocalMatrix a n ω0 ω1 G z y) x d0) x d1 =
      wickLocalMatrix a n (fun z => ω0 z + ω1 z)
        (wickDirectionalStateKernel n ω1 d1 (wickDirectionalStateKernel n ω0 d0 G)) x := by
  rw [wickBilocalMatrix_mixed_fderiv a n ω0 ω1 h0 h1,
    wickBilocalMatrix_diagonal a n ω0 ω1 h1]

theorem wickBilocalMatrix_mixed_fderiv_diagonal_smooth (a : Parameters) (n : ℕ)
    (ω0 ω1 : ParticleConfiguration n → Spacetime)
    (h0 : ω0.HasTemperateGrowth) (h1 : ω1.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (d0 d1 : Spacetime) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x =>
      fderiv ℝ (fun y => fderiv ℝ (fun z => wickBilocalMatrix a n ω0 ω1 G z y) x d0) x d1) := by
  simp_rw [wickBilocalMatrix_mixed_fderiv_diagonal a n ω0 ω1 h0 h1]
  exact wickLocalMatrix_smooth a n _ (h0.add h1) _

end AASCKleinGordon
