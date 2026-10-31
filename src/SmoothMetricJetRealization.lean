import NormalMetricSecondDerivatives

/-!
A concrete smooth, symmetric, locally nonsingular matrix field realizes every
original algebraic curvature tensor through the explicit normal-coordinate
second-derivative formula. Signature on the neighborhood and identification of
that formula with a geometric Levi-Civita curvature operator remain separate.
The canonical Lorentz value and dimension are inputs to this test realization.
-/
namespace AASCSemanticExhaustion
noncomputable section

def actualNormalSecondJet (R : curvatureSpace) : Tensor4 := fun a b c d =>
  fderiv ℝ (fun x => fderiv ℝ (fun y => normalMetricPolynomial R y a b) x
    (Pi.single c 1)) 0 (Pi.single d 1)

theorem actual_normal_second_jet_identification (R : curvatureSpace) :
    actualNormalSecondJet R = normalMetricHessian R := by
  funext a b c d
  exact normalMetricPolynomial_second_derivative R a b c d

theorem curvature_of_actual_normal_second_jet (R : curvatureSpace) :
    curvatureOfNormalHessian (actualNormalSecondJet R) = (R : Tensor4) := by
  rw [actual_normal_second_jet_identification]
  exact curvature_of_constructed_normal_hessian R

theorem smooth_symmetric_nonsingular_metric_jet_realization (R : curvatureSpace) :
    ∃ g : (Fin 4 → ℝ) → Tensor2, ∃ U : Set (Fin 4 → ℝ),
      IsOpen U ∧ 0 ∈ U ∧ g 0 = metric ∧
      (∀ x a b, g x a b = g x b a) ∧
      (∀ a b, ContDiff ℝ ⊤ (fun x => g x a b)) ∧
      (∀ x ∈ U, (g x).det ≠ 0) ∧
      (∀ a b, fderiv ℝ (fun x => g x a b) 0 = 0) ∧
      curvatureOfNormalHessian (fun a b c d =>
        fderiv ℝ (fun x => fderiv ℝ (fun y => g y a b) x (Pi.single c 1)) 0
          (Pi.single d 1)) = (R : Tensor4) := by
  obtain ⟨U, hopen, hzero, hdet⟩ := normalMetricPolynomial_nondegenerate_neighborhood R
  exact ⟨normalMetricPolynomial R, U, hopen, hzero,
    normalMetricPolynomial_at_zero R, normalMetricPolynomial_symmetric R,
    normalMetricPolynomial_smooth R, hdet,
    normalMetricPolynomial_first_derivative_zero R,
    curvature_of_actual_normal_second_jet R⟩

#print axioms actual_normal_second_jet_identification
#print axioms curvature_of_actual_normal_second_jet
#print axioms smooth_symmetric_nonsingular_metric_jet_realization
end
end AASCSemanticExhaustion
