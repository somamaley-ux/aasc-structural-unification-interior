import WickLorentzDensityTransport
import WickPoincareDerivativeTransport
import WickNativeAffineMetricTests

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory
open scoped BigOperators
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem wick_original_derivative_components_poincare (a : Parameters) (b : Spacetime) (L : ProperLorentzTransform)
    (s : ℝ) (u v : FiniteParticleCore) (x : Spacetime) :
    originalWickDerivativeComponents a s (corePoincare a b L u) (corePoincare a b L v)
      (b+spacetimeLorentzCLE L x) =
      (wickComplexMatrix (wickLorentzMatrix L⁻¹)).transpose *
        wickDerivativeMatrix a s u v x * wickComplexMatrix (wickLorentzMatrix L⁻¹) := by
  ext i j
  have inv (k : Fin 4) := spacetimeLorentz_inverse L⁻¹ (spacetimeCoordinateVector k)
  simp only [inv_inv] at inv
  have transport := wick_original_derivative_matrix_poincare a b L s u v
    (spacetimeLorentzCLE L⁻¹ (spacetimeCoordinateVector i))
    (spacetimeLorentzCLE L⁻¹ (spacetimeCoordinateVector j)) x
  rw [inv i, inv j] at transport
  change originalDerivativeWickMatrix a s (corePoincare a b L u) (corePoincare a b L v)
    (spacetimeCoordinateVector i) (spacetimeCoordinateVector j) (b+spacetimeLorentzCLE L x)=_
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

theorem wick_original_quantum_density_poincare (a : Parameters) (b : Spacetime) (L : ProperLorentzTransform)
    (s : ℝ) (u v : FiniteParticleCore) (G : NativeRealMatrix) (x : Spacetime) :
    wickQuantumActionDensity ((wickLorentzMatrix L⁻¹).transpose*G*wickLorentzMatrix L⁻¹)
      (originalWickDerivativeComponents a s (corePoincare a b L u) (corePoincare a b L v)
        (b+spacetimeLorentzCLE L x))
      (originalWickMassSquare a s (corePoincare a b L u) (corePoincare a b L v)
        (b+spacetimeLorentzCLE L x)) =
      wickQuantumActionDensity G (originalWickDerivativeComponents a s u v x)
        (originalWickMassSquare a s u v x) := by
  rw [wick_original_derivative_components_poincare, wick_original_mass_square_poincare]
  exact wick_quantum_density_congruence _ _ (wick_lorentz_matrix_det L⁻¹) _ _


theorem wick_poincare_integral_change (b : Spacetime) (L : ProperLorentzTransform)
    (f : Spacetime → ℂ) : (∫ x,f x)=(∫ x,f (b+spacetimeLorentzCLE L x)) := by
  have shift := integral_add_right_eq_self (μ:=(volume : Measure Spacetime)) f b
  have linear := (spacetimeLorentz_preserves_volume L).integral_comp
    (spacetimeLorentzCLE L).toHomeomorph.measurableEmbedding
    (fun x : Spacetime => f (x+b))
  rw [← shift, ← linear]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => congrArg f (add_comm _ _))

theorem wick_original_finite_action_poincare (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (u v : FiniteParticleCore)
    {Ω : TopologicalSpace.Opens CoordinatePoint} (H : MetricSourceProbe Ω) :
    wickOriginalFiniteAction a s (corePoincare a b L u) (corePoincare a b L v)
      (wickNativeAffineMetricTest b L H)=wickOriginalFiniteAction a s u v H := by
  unfold wickOriginalFiniteAction
  rw [wick_poincare_integral_change b L]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only
    rw [wick_native_affine_finite_metric, wick_original_quantum_density_poincare]
    have baseline := wick_original_quantum_density_poincare a b L s u v wickFlatMetric x
    rw [wick_lorentz_flat_metric] at baseline
    rw [baseline])

theorem wick_original_real_finite_action_poincare (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (u : FiniteParticleCore)
    {Ω : TopologicalSpace.Opens CoordinatePoint} (H : MetricSourceProbe Ω) :
    wickOriginalRealFiniteAction a s (corePoincare a b L u) (wickNativeAffineMetricTest b L H)=
      wickOriginalRealFiniteAction a s u H :=
  congrArg Complex.re (wick_original_finite_action_poincare a b L s u u H)

end AASCKleinGordon
