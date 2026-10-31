import KGWickMetricDensity

/-! Explicit flat raising and the computed coefficient of the SAME quantum
action. Symmetry belongs to the real metric test, not to an assumed quantum
commutation or Hermiticity law. All sixteen entries are contracted. -/
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
open scoped BigOperators
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickFlatMetric : NativeRealMatrix := nativeClockNormalMetric

theorem wick_flat_metric_square : wickFlatMetric * wickFlatMetric = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [wickFlatMetric,nativeClockNormalMetric,Matrix.mul_apply,Matrix.diagonal_apply,Fin.sum_univ_four]

theorem wick_flat_metric_inverse : wickFlatMetric⁻¹ = wickFlatMetric :=
  Matrix.inv_eq_right_inv wick_flat_metric_square

theorem wick_flat_metric_det : wickFlatMetric.det = -1 := by
  norm_num [wickFlatMetric,nativeClockNormalMetric,Matrix.det_diagonal,Fin.prod_univ_four]

theorem wick_flat_metric_volume : nativeRealClockVolume wickFlatMetric = 1 := by
  simp [nativeRealClockVolume,wick_flat_metric_det]

def originalWickDerivativeComponents (a : Parameters) (s : ℝ) (u v : FiniteParticleCore)
    (x : Spacetime) (i j : Fin 4) : ℂ :=
  originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector i) (spacetimeCoordinateVector j) x

def originalWickMassSquare (a : Parameters) (s : ℝ) (u v : FiniteParticleCore) (x : Spacetime) : ℂ :=
  ((massWaveNumber a)^2 : ℂ) * originalWickSquareMatrix a s u v x

def wickFlatSign (i : Fin 4) : ℝ := if i=0 then -1 else 1

def originalWickScalarStressRaisedMatrix (a : Parameters) (s : ℝ) (u v : FiniteParticleCore)
    (i j : Fin 4) (x : Spacetime) : ℂ :=
  (wickFlatSign i : ℂ)*(wickFlatSign j : ℂ)*originalWickScalarStressCandidateMatrix a s u v i j x

theorem original_wick_flat_density_eq_fixed_bracket (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (x : Spacetime) :
    wickQuantumActionDensity wickFlatMetric (originalWickDerivativeComponents a s u v x)
      (originalWickMassSquare a s u v x) = (-1/2 : ℂ)*originalWickScalarLagrangianMatrix a s u v x := by
  rw [wickQuantumActionDensity,wick_flat_metric_inverse,wick_flat_metric_volume]
  norm_num [wickFlatMetric,nativeClockNormalMetric,Matrix.diagonal_apply,Fin.sum_univ_four,
    originalWickDerivativeComponents,originalWickMassSquare,originalWickScalarLagrangianMatrix] <;>
    (try simp only [Fin.ext_iff]) <;> norm_num <;> ring

theorem original_wick_metric_density_coefficient (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (H : NativeRealMatrix) (hsym : ∀ i j,H i j=H j i) (x : Spacetime) :
    wickQuantumDensityVariation wickFlatMetric H (originalWickDerivativeComponents a s u v x)
      (originalWickMassSquare a s u v x) =
      (1/2 : ℂ)*∑ i,∑ j,(H i j : ℂ)*originalWickScalarStressRaisedMatrix a s u v i j x := by
  have h01 := hsym 1 0
  have h02 := hsym 2 0
  have h03 := hsym 3 0
  have h12 := hsym 2 1
  have h13 := hsym 3 1
  have h23 := hsym 3 2
  unfold wickQuantumDensityVariation
  rw [wick_flat_metric_inverse,wick_flat_metric_volume]
  norm_num [wickFlatMetric,nativeClockNormalMetric,Matrix.trace,Matrix.diag,Matrix.mul_apply,
    Matrix.diagonal_apply,Fin.sum_univ_four,originalWickDerivativeComponents,originalWickMassSquare,
    originalWickScalarStressRaisedMatrix,wickFlatSign,originalWickScalarStressCandidateMatrix,
    wickFlatMetricComponent,originalWickScalarLagrangianMatrix,h01,h02,h03,h12,h13,h23] <;>
    (try simp only [Fin.ext_iff]) <;> norm_num <;> ring

end AASCKleinGordon
