import WickLorentzBilocalTransport

noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon

theorem wick_fderiv_linear_transport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E ≃L[ℝ] E) (f g : E → ℂ) (x d : E)
    (hf : DifferentiableAt ℝ f (L x)) (same : ∀ z,f (L z)=g z) :
    fderiv ℝ f (L x) (L d)=fderiv ℝ g x d := by
  have eq : f ∘ L = g := funext same
  have chain := fderiv_comp x hf L.differentiableAt
  have evaluated := congrArg (fun T => T d) chain
  simpa only [eq, ContinuousLinearEquiv.fderiv, ContinuousLinearMap.comp_apply] using evaluated.symm

theorem wick_original_first_derivative_lorentz (a : Parameters) (L : ProperLorentzTransform)
    (s : ℝ) (u v : FiniteParticleCore) (d x y : Spacetime) :
    originalFirstDerivativeWickBilocalCore a s (coreLorentz a L u) (coreLorentz a L v)
      (spacetimeLorentzCLE L d) (spacetimeLorentzCLE L x) (spacetimeLorentzCLE L y) =
      originalFirstDerivativeWickBilocalCore a s u v d x y := by
  rw [← originalWickBilocalCore_fderiv_left, ← originalWickBilocalCore_fderiv_left]
  apply wick_fderiv_linear_transport (spacetimeLorentzCLE L)
  · exact ((originalWickBilocalCore_left_smooth a s (coreLorentz a L u)
      (coreLorentz a L v) (spacetimeLorentzCLE L y)).differentiable (by simp)) _
  · intro z
    exact wick_original_bilocal_lorentz a L s u v z y

theorem wick_original_derivative_bilocal_lorentz (a : Parameters) (L : ProperLorentzTransform)
    (s : ℝ) (u v : FiniteParticleCore) (d e x y : Spacetime) :
    originalDerivativeWickBilocalCore a s (coreLorentz a L u) (coreLorentz a L v)
      (spacetimeLorentzCLE L d) (spacetimeLorentzCLE L e)
      (spacetimeLorentzCLE L x) (spacetimeLorentzCLE L y) =
      originalDerivativeWickBilocalCore a s u v d e x y := by
  rw [← originalFirstDerivativeWickBilocalCore_fderiv_right,
    ← originalFirstDerivativeWickBilocalCore_fderiv_right]
  apply wick_fderiv_linear_transport (spacetimeLorentzCLE L)
  · exact ((originalFirstDerivativeWickBilocalCore_right_smooth a s (coreLorentz a L u)
      (coreLorentz a L v) (spacetimeLorentzCLE L d) (spacetimeLorentzCLE L x)).differentiable
        (by simp)) _
  · intro z
    exact wick_original_first_derivative_lorentz a L s u v d x z

theorem wick_original_derivative_matrix_lorentz (a : Parameters) (L : ProperLorentzTransform)
    (s : ℝ) (u v : FiniteParticleCore) (d e x : Spacetime) :
    originalDerivativeWickMatrix a s (coreLorentz a L u) (coreLorentz a L v)
      (spacetimeLorentzCLE L d) (spacetimeLorentzCLE L e) (spacetimeLorentzCLE L x) =
      originalDerivativeWickMatrix a s u v d e x :=
  wick_original_derivative_bilocal_lorentz a L s u v d e x x

theorem wick_original_mass_square_lorentz (a : Parameters) (L : ProperLorentzTransform)
    (s : ℝ) (u v : FiniteParticleCore) (x : Spacetime) :
    originalWickMassSquare a s (coreLorentz a L u) (coreLorentz a L v)
      (spacetimeLorentzCLE L x) = originalWickMassSquare a s u v x := by
  unfold originalWickMassSquare
  rw [wick_original_square_lorentz]

end AASCKleinGordon
