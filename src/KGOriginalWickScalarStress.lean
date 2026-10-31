import KGOriginalDerivativeWickAssembly
import KGSchwartzDifferential

/-! A quantum scalar stress CANDIDATE from the actual original Wick products,
with the fixed scalar action's coefficients and signature. No action-variation,
Ward, operational-source or charge-matching identity is assumed or claimed. -/
noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

def wickFlatMetricComponent (μ ν : Fin 4) : ℝ :=
  if μ=ν then (if μ=0 then -1 else 1) else 0

theorem wickFlatMetricComponent_symmetric (μ ν : Fin 4) :
    wickFlatMetricComponent μ ν = wickFlatMetricComponent ν μ := by
  by_cases h : μ=ν
  · subst ν; rfl
  · simp [wickFlatMetricComponent,h,Ne.symm h]

def originalWickScalarLagrangianMatrix (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (x : Spacetime) : ℂ :=
  -originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector 0) (spacetimeCoordinateVector 0) x +
    originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector 1) (spacetimeCoordinateVector 1) x +
    originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector 2) (spacetimeCoordinateVector 2) x +
    originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector 3) (spacetimeCoordinateVector 3) x +
    ((massWaveNumber a)^2 : ℂ) * originalWickSquareMatrix a s u v x

def originalWickScalarStressCandidateMatrix (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (μ ν : Fin 4) (x : Spacetime) : ℂ :=
  (1/2 : ℂ) *
    (originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector μ) (spacetimeCoordinateVector ν) x +
      originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector ν) (spacetimeCoordinateVector μ) x) -
    ((wickFlatMetricComponent μ ν : ℂ)/2) * originalWickScalarLagrangianMatrix a s u v x

def originalWickScalarLagrangianSesqForm (a : Parameters) (s : ℝ) :
    FiniteParticleCore →ₗ⋆[ℂ] FiniteParticleCore →ₗ[ℂ] (𝓢(Spacetime,ℂ) →L[ℂ] ℂ) :=
  (-1 : ℂ) • originalDerivativeWickDistributionSesqForm a s (spacetimeCoordinateVector 0) (spacetimeCoordinateVector 0) +
    originalDerivativeWickDistributionSesqForm a s (spacetimeCoordinateVector 1) (spacetimeCoordinateVector 1) +
    originalDerivativeWickDistributionSesqForm a s (spacetimeCoordinateVector 2) (spacetimeCoordinateVector 2) +
    originalDerivativeWickDistributionSesqForm a s (spacetimeCoordinateVector 3) (spacetimeCoordinateVector 3) +
    ((massWaveNumber a)^2 : ℂ) • originalWickSquareDistributionSesqForm a s

def originalWickScalarStressCandidateSesqForm (a : Parameters) (s : ℝ) (μ ν : Fin 4) :
    FiniteParticleCore →ₗ⋆[ℂ] FiniteParticleCore →ₗ[ℂ] (𝓢(Spacetime,ℂ) →L[ℂ] ℂ) :=
  (1/2 : ℂ) •
    (originalDerivativeWickDistributionSesqForm a s (spacetimeCoordinateVector μ) (spacetimeCoordinateVector ν) +
      originalDerivativeWickDistributionSesqForm a s (spacetimeCoordinateVector ν) (spacetimeCoordinateVector μ)) +
    (-((wickFlatMetricComponent μ ν : ℂ)/2)) • originalWickScalarLagrangianSesqForm a s

theorem originalWickScalarLagrangianMatrix_smooth (a : Parameters) (s : ℝ) (u v : FiniteParticleCore) :
    ContDiff ℝ (⊤ : ℕ∞) (originalWickScalarLagrangianMatrix a s u v) :=
  (((((originalDerivativeWickMatrix_smooth a s u v _ _).neg.add
    (originalDerivativeWickMatrix_smooth a s u v _ _)).add
    (originalDerivativeWickMatrix_smooth a s u v _ _)).add
    (originalDerivativeWickMatrix_smooth a s u v _ _)).add
    (contDiff_const.mul (originalWickSquareMatrix_smooth a s u v)))

theorem originalWickScalarStressCandidateMatrix_smooth (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (μ ν : Fin 4) :
    ContDiff ℝ (⊤ : ℕ∞) (originalWickScalarStressCandidateMatrix a s u v μ ν) :=
  (contDiff_const.mul ((originalDerivativeWickMatrix_smooth a s u v _ _).add
    (originalDerivativeWickMatrix_smooth a s u v _ _))).sub
      (contDiff_const.mul (originalWickScalarLagrangianMatrix_smooth a s u v))

theorem originalWickScalarStressCandidateMatrix_symmetric (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (μ ν : Fin 4) (x : Spacetime) :
    originalWickScalarStressCandidateMatrix a s u v μ ν x =
      originalWickScalarStressCandidateMatrix a s u v ν μ x := by
  unfold originalWickScalarStressCandidateMatrix
  rw [wickFlatMetricComponent_symmetric μ ν, add_comm]

theorem originalWickScalarLagrangianMatrix_test_integrable (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (h : 𝓢(Spacetime,ℂ)) :
    Integrable (fun x => h x * originalWickScalarLagrangianMatrix a s u v x) := by
  have hd (i : Fin 4) := originalDerivativeWickMatrix_test_integrable a s u v
    (spacetimeCoordinateVector i) (spacetimeCoordinateVector i) h
  have hs := originalWickSquareMatrix_test_integrable a s u v h
  convert ((((hd 0).neg.add (hd 1)).add (hd 2)).add (hd 3)).add
    (hs.const_mul (((massWaveNumber a)^2 : ℂ))) using 1
  funext x
  simp only [originalWickScalarLagrangianMatrix, Pi.add_apply, Pi.neg_apply]
  ring

theorem originalWickScalarLagrangianSesqForm_pairing (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (h : 𝓢(Spacetime,ℂ)) :
    originalWickScalarLagrangianSesqForm a s u v h =
      ∫ x,h x * originalWickScalarLagrangianMatrix a s u v x := by
  have hd (i : Fin 4) := originalDerivativeWickMatrix_test_integrable a s u v
    (spacetimeCoordinateVector i) (spacetimeCoordinateVector i) h
  have hs := originalWickSquareMatrix_test_integrable a s u v h
  have hneg0 : Integrable (fun x =>
      -(h x * originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector 0) (spacetimeCoordinateVector 0) x)) :=
    (hd 0).neg
  have h01 : Integrable (fun x =>
      -(h x * originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector 0) (spacetimeCoordinateVector 0) x) +
      h x * originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector 1) (spacetimeCoordinateVector 1) x) :=
    (hd 0).neg.add (hd 1)
  have h012 : Integrable (fun x =>
      -(h x * originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector 0) (spacetimeCoordinateVector 0) x) +
      h x * originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector 1) (spacetimeCoordinateVector 1) x +
      h x * originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector 2) (spacetimeCoordinateVector 2) x) :=
    h01.add (hd 2)
  have h0123 : Integrable (fun x =>
      -(h x * originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector 0) (spacetimeCoordinateVector 0) x) +
      h x * originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector 1) (spacetimeCoordinateVector 1) x +
      h x * originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector 2) (spacetimeCoordinateVector 2) x +
      h x * originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector 3) (spacetimeCoordinateVector 3) x) :=
    h012.add (hd 3)
  have hp (x : Spacetime) : h x * originalWickScalarLagrangianMatrix a s u v x =
      - (h x * originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector 0) (spacetimeCoordinateVector 0) x) +
      h x * originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector 1) (spacetimeCoordinateVector 1) x +
      h x * originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector 2) (spacetimeCoordinateVector 2) x +
      h x * originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector 3) (spacetimeCoordinateVector 3) x +
      ((massWaveNumber a)^2 : ℂ) * (h x * originalWickSquareMatrix a s u v x) := by
    unfold originalWickScalarLagrangianMatrix
    ring
  simp_rw [hp]
  rw [integral_add h0123 (hs.const_mul (((massWaveNumber a)^2 : ℂ))),
    integral_add h012 (hd 3), integral_add h01 (hd 2), integral_add hneg0 (hd 1),
    integral_neg, integral_const_mul]
  simp only [originalWickScalarLagrangianSesqForm, LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul,
    originalDerivativeWickDistributionSesqForm_pairing, originalWickSquareDistributionSesqForm_pairing,
    neg_one_mul]

theorem originalWickScalarStressCandidateSesqForm_pairing (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (μ ν : Fin 4) (h : 𝓢(Spacetime,ℂ)) :
    originalWickScalarStressCandidateSesqForm a s μ ν u v h =
      ∫ x,h x * originalWickScalarStressCandidateMatrix a s u v μ ν x := by
  have h0 := originalDerivativeWickMatrix_test_integrable a s u v
    (spacetimeCoordinateVector μ) (spacetimeCoordinateVector ν) h
  have h1 := originalDerivativeWickMatrix_test_integrable a s u v
    (spacetimeCoordinateVector ν) (spacetimeCoordinateVector μ) h
  have hL := originalWickScalarLagrangianMatrix_test_integrable a s u v h
  have h01 : Integrable (fun x =>
      h x * originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector μ) (spacetimeCoordinateVector ν) x +
      h x * originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector ν) (spacetimeCoordinateVector μ) x) :=
    h0.add h1
  have hA : Integrable (fun x => (1/2 : ℂ) *
      (h x * originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector μ) (spacetimeCoordinateVector ν) x +
      h x * originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector ν) (spacetimeCoordinateVector μ) x)) :=
    h01.const_mul _
  have hp (x : Spacetime) : h x * originalWickScalarStressCandidateMatrix a s u v μ ν x =
      (1/2 : ℂ) * (h x * originalDerivativeWickMatrix a s u v
        (spacetimeCoordinateVector μ) (spacetimeCoordinateVector ν) x +
        h x * originalDerivativeWickMatrix a s u v
        (spacetimeCoordinateVector ν) (spacetimeCoordinateVector μ) x) -
      ((wickFlatMetricComponent μ ν : ℂ)/2) * (h x * originalWickScalarLagrangianMatrix a s u v x) := by
    unfold originalWickScalarStressCandidateMatrix
    ring
  simp_rw [hp]
  rw [integral_sub hA (hL.const_mul ((wickFlatMetricComponent μ ν : ℂ)/2)), integral_const_mul,
    integral_const_mul, integral_add h0 h1]
  simp only [originalWickScalarStressCandidateSesqForm, LinearMap.add_apply,
    LinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul,
    originalDerivativeWickDistributionSesqForm_pairing, originalWickScalarLagrangianSesqForm_pairing]
  ring

theorem originalWickScalarStressCandidateMatrix_vacuum (a : Parameters) (s : ℝ)
    (μ ν : Fin 4) (x : Spacetime) :
    originalWickScalarStressCandidateMatrix a s vacuumCore vacuumCore μ ν x = 0 := by
  simp [originalWickScalarStressCandidateMatrix, originalWickScalarLagrangianMatrix,
    originalDerivativeWickMatrix_vacuum, originalWickSquareMatrix_vacuum]

theorem originalWickScalarStressCandidateSesqForm_vacuum (a : Parameters) (s : ℝ) (μ ν : Fin 4) :
    originalWickScalarStressCandidateSesqForm a s μ ν vacuumCore vacuumCore = 0 := by
  ext h
  simp [originalWickScalarStressCandidateSesqForm_pairing, originalWickScalarStressCandidateMatrix_vacuum]

end AASCKleinGordon
