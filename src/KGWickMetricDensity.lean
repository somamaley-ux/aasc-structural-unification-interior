import KGOriginalWickScalarStress
import NativeClockDensityContinuity
import Mathlib.Analysis.Complex.RealDeriv

/-! The fixed scalar action density with arbitrary actual complex quadratic
coefficients. Inverse and volume are the actual nonsingular matrix operations.
The derivative is computed, not assumed or defined as stress pairing. -/
noncomputable section
set_option maxHeartbeats 4000000
open scoped BigOperators Topology
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickQuantumActionDensity (G : NativeRealMatrix)
    (D : Fin 4 → Fin 4 → ℂ) (M : ℂ) : ℂ :=
  (-1/2 : ℂ) * (nativeRealClockVolume G : ℂ) *
    ((∑ i,∑ j,(G⁻¹ i j : ℂ) * D i j) + M)

def wickQuantumDensityVariation (G H : NativeRealMatrix)
    (D : Fin 4 → Fin 4 → ℂ) (M : ℂ) : ℂ :=
  (-1/2 : ℂ) * (nativeRealClockVolume G : ℂ) *
    ((((Matrix.trace (G⁻¹ * H) : ℝ) : ℂ)/2) *
      ((∑ i,∑ j,(G⁻¹ i j : ℂ) * D i j) + M) +
      ∑ i,∑ j,((-G⁻¹ * H * G⁻¹) i j : ℂ) * D i j)

theorem wick_quantum_density_path_hasDerivAt (G H : NativeRealMatrix)
    (hn : G.det ≠ 0) (D : Fin 4 → Fin 4 → ℂ) (M : ℂ) :
    HasDerivAt (fun t : ℝ => wickQuantumActionDensity (G+t • H) D M)
      (wickQuantumDensityVariation G H D M) 0 := by
  have hr : IsUnit G.det := isUnit_iff_ne_zero.mpr hn
  have hGB : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hr
  have hBG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hr
  have hk : HasDerivAt (fun t : ℝ => ∑ i,∑ j,((G+t • H)⁻¹ i j : ℂ) * D i j)
      (∑ i,∑ j,((-G⁻¹ * H * G⁻¹) i j : ℂ) * D i j) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.fun_sum
    intro j _
    exact ((native_real_metric_inverse_entry_hasDerivAt G G⁻¹ H hGB hBG i j).ofReal_comp).mul_const _
  have hv := (native_real_clock_volume_path_hasDerivAt G G⁻¹ H hGB hn).ofReal_comp
  have hd := (hv.const_mul (-1/2 : ℂ)).mul (hk.add_const M)
  convert hd using 1 <;>
    simp [wickQuantumActionDensity,wickQuantumDensityVariation] <;> ring

theorem wick_quantum_density_path_derivative_at (G H : NativeRealMatrix)
    (D : Fin 4 → Fin 4 → ℂ) (M : ℂ) (t : ℝ) (hn : (G+t • H).det ≠ 0) :
    HasDerivAt (fun r : ℝ => wickQuantumActionDensity (G+r • H) D M)
      (wickQuantumDensityVariation (G+t • H) H D M) t := by
  have hd := wick_quantum_density_path_hasDerivAt (G+t • H) H hn D M
  have hd' : HasDerivAt (fun r : ℝ => wickQuantumActionDensity (G+t • H+r • H) D M)
      (wickQuantumDensityVariation (G+t • H) H D M) (t-t) := by
    simpa only [id_eq,sub_self] using hd
  have hh := hd'.scomp (h := fun r : ℝ => r-t) t ((hasDerivAt_id t).sub_const t)
  have heq : (fun r : ℝ => wickQuantumActionDensity ((G+t • H)+(r-t) • H) D M) =
      (fun r : ℝ => wickQuantumActionDensity (G+r • H) D M) := by
    funext r
    congr 1
    module
  simpa only [Function.comp_def,heq,one_smul] using hh

end AASCKleinGordon
