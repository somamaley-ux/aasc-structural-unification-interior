import WickLorentzDerivativeTransport

noncomputable section
set_option maxHeartbeats 1500000
open scoped BigOperators
namespace AASCKleinGordon

theorem wick_spacetime_coordinate_expansion (d : Spacetime) :
    d=∑ i : Fin 4,(d i) • spacetimeCoordinateVector i := by
  ext j
  simp [spacetimeCoordinateVector, EuclideanSpace.single_apply, Pi.single_apply]

theorem wick_linear_coordinate_expansion (T : Spacetime →L[ℝ] ℂ) (d : Spacetime) :
    T d=∑ i : Fin 4,(d i : ℂ)*T (spacetimeCoordinateVector i) := by
  conv_lhs => rw [wick_spacetime_coordinate_expansion d]
  simp only [map_sum, map_smul, RCLike.real_smul_eq_coe_mul]
  rfl

theorem wick_first_derivative_direction_expansion (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (d x y : Spacetime) :
    originalFirstDerivativeWickBilocalCore a s u v d x y =
      ∑ i : Fin 4,(d i : ℂ)*originalFirstDerivativeWickBilocalCore a s u v
        (spacetimeCoordinateVector i) x y := by
  simp_rw [← originalWickBilocalCore_fderiv_left]
  exact wick_linear_coordinate_expansion _ d

theorem wick_derivative_direction_expansion (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (d e x y : Spacetime) :
    originalDerivativeWickBilocalCore a s u v d e x y =
      ∑ i : Fin 4,∑ j : Fin 4,(d i : ℂ)*(e j : ℂ)*
        originalDerivativeWickBilocalCore a s u v
          (spacetimeCoordinateVector i) (spacetimeCoordinateVector j) x y := by
  rw [← originalFirstDerivativeWickBilocalCore_fderiv_right]
  have expansion : (fun z => originalFirstDerivativeWickBilocalCore a s u v d x z) =
      (fun z => ∑ i : Fin 4,(d i : ℂ)*originalFirstDerivativeWickBilocalCore a s u v
        (spacetimeCoordinateVector i) x z) :=
    funext (fun z => wick_first_derivative_direction_expansion a s u v d x z)
  rw [expansion]
  rw [wick_finite_weighted_directional_derivative]
  · apply Finset.sum_congr rfl
    intro i _
    rw [wick_linear_coordinate_expansion
      (fderiv ℝ (fun z => originalFirstDerivativeWickBilocalCore a s u v
        (spacetimeCoordinateVector i) x z) y) e]
    simp only [map_sum, map_smul, RCLike.real_smul_eq_coe_mul, Finset.mul_sum,
      originalFirstDerivativeWickBilocalCore_fderiv_right, mul_assoc]
  · intro i _
    exact ((originalFirstDerivativeWickBilocalCore_right_smooth a s u v
      (spacetimeCoordinateVector i) x).differentiable (by simp)) y

theorem wick_derivative_matrix_direction_expansion (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (d e x : Spacetime) :
    originalDerivativeWickMatrix a s u v d e x =
      ∑ i : Fin 4,∑ j : Fin 4,(d i : ℂ)*(e j : ℂ)*
        originalWickDerivativeComponents a s u v x i j :=
  wick_derivative_direction_expansion a s u v d e x x

end AASCKleinGordon
