import WickDerivativeComponentExpansion
import WickMetricDensityCongruence
import WickLorentzMetricCoordinates

noncomputable section
set_option maxHeartbeats 1500000
open scoped BigOperators
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickDerivativeMatrix (a : Parameters) (s : ℝ) (u v : FiniteParticleCore)
    (x : Spacetime) : Matrix (Fin 4) (Fin 4) ℂ :=
  originalWickDerivativeComponents a s u v x

theorem wick_original_derivative_components_lorentz (a : Parameters) (L : ProperLorentzTransform)
    (s : ℝ) (u v : FiniteParticleCore) (x : Spacetime) :
    originalWickDerivativeComponents a s (coreLorentz a L u) (coreLorentz a L v)
      (spacetimeLorentzCLE L x) =
      (wickComplexMatrix (wickLorentzMatrix L⁻¹)).transpose *
        wickDerivativeMatrix a s u v x * wickComplexMatrix (wickLorentzMatrix L⁻¹) := by
  ext i j
  have inv (k : Fin 4) := spacetimeLorentz_inverse L⁻¹ (spacetimeCoordinateVector k)
  simp only [inv_inv] at inv
  have transport := wick_original_derivative_matrix_lorentz a L s u v
    (spacetimeLorentzCLE L⁻¹ (spacetimeCoordinateVector i))
    (spacetimeLorentzCLE L⁻¹ (spacetimeCoordinateVector j)) x
  rw [inv i, inv j] at transport
  change originalDerivativeWickMatrix a s (coreLorentz a L u) (coreLorentz a L v)
    (spacetimeCoordinateVector i) (spacetimeCoordinateVector j) (spacetimeLorentzCLE L x)=_
  rw [transport, wick_derivative_matrix_direction_expansion]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  change _=(wickLorentzMatrix L⁻¹ l i : ℂ)*_*(wickLorentzMatrix L⁻¹ k j : ℂ)
  rw [wick_lorentz_matrix_apply, wick_lorentz_matrix_apply]
  dsimp only [wickDerivativeMatrix]
  ring

theorem wick_original_quantum_density_lorentz (a : Parameters) (L : ProperLorentzTransform)
    (s : ℝ) (u v : FiniteParticleCore) (G : NativeRealMatrix) (x : Spacetime) :
    wickQuantumActionDensity ((wickLorentzMatrix L⁻¹).transpose*G*wickLorentzMatrix L⁻¹)
      (originalWickDerivativeComponents a s (coreLorentz a L u) (coreLorentz a L v)
        (spacetimeLorentzCLE L x))
      (originalWickMassSquare a s (coreLorentz a L u) (coreLorentz a L v)
        (spacetimeLorentzCLE L x)) =
      wickQuantumActionDensity G (originalWickDerivativeComponents a s u v x)
        (originalWickMassSquare a s u v x) := by
  rw [wick_original_derivative_components_lorentz, wick_original_mass_square_lorentz]
  exact wick_quantum_density_congruence _ _ (wick_lorentz_matrix_det L⁻¹) _ _

end AASCKleinGordon
