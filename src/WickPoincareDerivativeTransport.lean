import WickTranslationBilocalTransport
import WickLorentzDerivativeTransport

noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon

theorem wick_fderiv_affine_transport (L : Spacetime ≃L[ℝ] Spacetime) (b : Spacetime)
    (f g : Spacetime → ℂ) (x d : Spacetime)
    (hf : DifferentiableAt ℝ f (b+L x)) (same : ∀ z,f (b+L z)=g z) :
    fderiv ℝ f (b+L x) (L d)=fderiv ℝ g x d := by
  have eq : f ∘ (fun z => b+L z)=g := funext same
  have shift : HasFDerivAt (fun z => b+L z) L.toContinuousLinearMap x :=
    L.hasFDerivAt.const_add b
  have chain := fderiv_comp x hf shift.differentiableAt
  rw [eq,shift.fderiv] at chain
  exact (congrArg (fun T => T d) chain).symm

theorem wick_original_first_derivative_poincare (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (u v : FiniteParticleCore) (d x y : Spacetime) :
    originalFirstDerivativeWickBilocalCore a s (corePoincare a b L u) (corePoincare a b L v)
      (spacetimeLorentzCLE L d) (b+spacetimeLorentzCLE L x) (b+spacetimeLorentzCLE L y) =
      originalFirstDerivativeWickBilocalCore a s u v d x y := by
  rw [← originalWickBilocalCore_fderiv_left, ← originalWickBilocalCore_fderiv_left]
  apply wick_fderiv_affine_transport (spacetimeLorentzCLE L) b
  · exact ((originalWickBilocalCore_left_smooth a s (corePoincare a b L u)
      (corePoincare a b L v) (b+spacetimeLorentzCLE L y)).differentiable (by simp)) _
  · intro z
    exact wick_original_bilocal_poincare a b L s u v z y

theorem wick_original_derivative_bilocal_poincare (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (u v : FiniteParticleCore) (d e x y : Spacetime) :
    originalDerivativeWickBilocalCore a s (corePoincare a b L u) (corePoincare a b L v)
      (spacetimeLorentzCLE L d) (spacetimeLorentzCLE L e)
      (b+spacetimeLorentzCLE L x) (b+spacetimeLorentzCLE L y) =
      originalDerivativeWickBilocalCore a s u v d e x y := by
  rw [← originalFirstDerivativeWickBilocalCore_fderiv_right,
    ← originalFirstDerivativeWickBilocalCore_fderiv_right]
  apply wick_fderiv_affine_transport (spacetimeLorentzCLE L) b
  · exact ((originalFirstDerivativeWickBilocalCore_right_smooth a s (corePoincare a b L u)
      (corePoincare a b L v) (spacetimeLorentzCLE L d)
      (b+spacetimeLorentzCLE L x)).differentiable (by simp)) _
  · intro z
    exact wick_original_first_derivative_poincare a b L s u v d x z

theorem wick_original_derivative_matrix_poincare (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (u v : FiniteParticleCore) (d e x : Spacetime) :
    originalDerivativeWickMatrix a s (corePoincare a b L u) (corePoincare a b L v)
      (spacetimeLorentzCLE L d) (spacetimeLorentzCLE L e) (b+spacetimeLorentzCLE L x) =
      originalDerivativeWickMatrix a s u v d e x :=
  wick_original_derivative_bilocal_poincare a b L s u v d e x x

theorem wick_original_mass_square_poincare (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (u v : FiniteParticleCore) (x : Spacetime) :
    originalWickMassSquare a s (corePoincare a b L u) (corePoincare a b L v)
      (b+spacetimeLorentzCLE L x) = originalWickMassSquare a s u v x := by
  unfold originalWickMassSquare originalWickSquareMatrix
  rw [wick_original_bilocal_poincare]

end AASCKleinGordon
