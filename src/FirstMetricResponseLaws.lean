import CubicGaugeRealization

/-!
Explicit first-response/order laws on an arbitrary response to actual metric
fields. No contraction syntax, Ricci expansion, curvature-factorization field,
or coefficient-constancy field occurs. The manuscript's S6 is to be matched to
these local affine laws while the other geometric comparison conditions remain
visible. This is the core needed for response exhaustion, not the complete
S17/S18 closed-source and active-response theorem.
-/
namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0

def NormalizedSmoothMetricGerm (g : MetricField) : Prop :=
  MetricFieldSymmetric g ∧ (∀ a b, ContDiffAt ℝ ⊤ (fun x => g x a b) 0) ∧
    g 0 = metric ∧ (∀ a b, fderiv ℝ (fun x => g x a b) 0 = 0)

def flatMetricField : MetricField := fun _ => metric

def MetricFirstResponseAffine (E : MetricFieldResponse) : Prop :=
  (∀ g h k : MetricField,
    NormalizedSmoothMetricGerm g → NormalizedSmoothMetricGerm h → NormalizedSmoothMetricGerm k →
    (∀ a b c d, scalarSecondPartial (fun x => k x a b) 0 c d =
      scalarSecondPartial (fun x => g x a b) 0 c d + scalarSecondPartial (fun x => h x a b) 0 c d) →
      E k 0 = E g 0 + E h 0 - E flatMetricField 0) ∧
  (∀ r : ℝ, ∀ g k : MetricField,
    NormalizedSmoothMetricGerm g → NormalizedSmoothMetricGerm k →
    (∀ a b c d, scalarSecondPartial (fun x => k x a b) 0 c d =
      r * scalarSecondPartial (fun x => g x a b) 0 c d) →
      E k 0 = r • (E g 0 - E flatMetricField 0) + E flatMetricField 0)

def MetricResponseSymmetric (E : MetricFieldResponse) : Prop :=
  ∀ g p a b, E g p a b = E g p b a

theorem hessianMetricPolynomial_normalized (H : metricHessianSpace) :
    NormalizedSmoothMetricGerm (hessianMetricPolynomial H) :=
  ⟨hessianMetricPolynomial_symmetric H,
    (fun a b => (hessianMetricPolynomial_smooth H a b).contDiffAt),
    hessianMetricPolynomial_zero H, hessianMetricPolynomial_first_zero H⟩

theorem hessianMetricPolynomial_flat : hessianMetricPolynomial 0 = flatMetricField := by
  funext x a b
  simp [hessianMetricPolynomial, hessianRow, quadraticPolynomial, flatMetricField]

theorem metric_response_hessian_affine_from_first_response (E : MetricFieldResponse)
    (firstResponse : MetricFirstResponseAffine E) : HessianAffine (metricHessianResponseAt E 0) := by
  constructor
  · intro H K
    simp only [metricHessianResponseAt_origin]
    rw [hessianMetricPolynomial_flat]
    apply firstResponse.1 _ _ _ (hessianMetricPolynomial_normalized H)
      (hessianMetricPolynomial_normalized K) (hessianMetricPolynomial_normalized (H + K))
    intro a b c d
    rw [hessian_metric_scalarSecond, hessian_metric_scalarSecond, hessian_metric_scalarSecond]
    rfl
  · intro r H
    simp only [metricHessianResponseAt_origin]
    rw [hessianMetricPolynomial_flat]
    apply firstResponse.2 r _ _ (hessianMetricPolynomial_normalized H)
      (hessianMetricPolynomial_normalized (r • H))
    intro a b c d
    rw [hessian_metric_scalarSecond, hessian_metric_scalarSecond]
    rfl

theorem metric_response_hessian_symmetric (E : MetricFieldResponse)
    (symmetric : MetricResponseSymmetric E) : HessianSymmetric (metricHessianResponseAt E 0) := by
  intro H a b
  rw [metricHessianResponseAt_origin]
  exact symmetric _ 0 a b

#print axioms hessianMetricPolynomial_normalized
#print axioms hessianMetricPolynomial_flat
#print axioms metric_response_hessian_affine_from_first_response
#print axioms metric_response_hessian_symmetric
end
end AASCSemanticExhaustion
