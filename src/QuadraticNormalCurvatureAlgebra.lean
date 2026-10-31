import C2GeneralCurvatureFormula

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 8192

abbrev ConnectionValue := Fin 4 → Fin 4 → Fin 4 → ℝ

def compatibleMetricFirstJet (G : Tensor2) (Γ : ConnectionValue) : ConnectionValue := fun a b c =>
  (∑ i : Fin 4, Γ i c a * G i b) + (∑ i : Fin 4, Γ i c b * G a i)

def quadraticMetricJetCorrection (G : Tensor2) (S : ConnectionValue) (Q : ConnectionValue) : Tensor4 :=
  fun a b c d =>
    (∑ u : Fin 4, S a b u * Q u c d) +
    (∑ i : Fin 4, (Q i a c * S i b d + S i b c * Q i a d)) +
    (∑ j : Fin 4, (S a j c * Q j b d + Q j b c * S a j d)) +
    (∑ i : Fin 4, ∑ j : Fin 4, G i j * (Q i a c * Q j b d + Q j b c * Q i a d))

theorem curvatureOfNormalHessian_add (H K : Tensor4) :
    curvatureOfNormalHessian (H + K) = curvatureOfNormalHessian H + curvatureOfNormalHessian K := by
  funext a b c d
  simp only [curvatureOfNormalHessian, Pi.add_apply]
  ring

/-- The quadratic normalizing correction has exactly the connection-product
curvature correction. This is a finite algebra identity, not a transport axiom. -/
theorem quadratic_normalizing_curvature_correction (G : Tensor2) (Γ : ConnectionValue)
    (symmetric : ∀ i j, G i j = G j i) (torsion : ∀ i a b, Γ i a b = Γ i b a) (a b c d : Fin 4) :
    curvatureOfNormalHessian
      (quadraticMetricJetCorrection G (compatibleMetricFirstJet G Γ) (fun i u v => -Γ i u v)) a b c d =
      (∑ k : Fin 4, Γ k a d * (∑ e : Fin 4, G k e * Γ e b c)) -
        (∑ k : Fin 4, Γ k a c * (∑ e : Fin 4, G k e * Γ e b d)) := by
  simp only [curvatureOfNormalHessian, quadraticMetricJetCorrection, compatibleMetricFirstJet,
    Fin.sum_univ_four]
  simp only [symmetric, torsion]
  ring

#print axioms curvatureOfNormalHessian_add
#print axioms quadratic_normalizing_curvature_correction
end
end AASCSemanticExhaustion
