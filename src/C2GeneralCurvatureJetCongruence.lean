import GeneralFlatChartCurvature

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0
set_option autoImplicit false

theorem lowerChristoffel_metric_twojet_congr (g h : MetricField) (p : CoordinatePoint)
    (equal : MetricTwoJetEqualAt g h p) (a b c : Fin 4) :
    lowerChristoffel g p a b c = lowerChristoffel h p a b c := by
  simp only [lowerChristoffel, metricPartial, equal.2.1]

theorem leviCivita_metric_twojet_congr (g h : MetricField) (p : CoordinatePoint)
    (equal : MetricTwoJetEqualAt g h p) (a b c : Fin 4) :
    leviCivitaCoefficients g p a b c = leviCivitaCoefficients h p a b c := by
  simp only [leviCivitaCoefficients, equal.1, lowerChristoffel_metric_twojet_congr g h p equal]

theorem c2_general_curvature_twojet_congr (g h : MetricField) (p : CoordinatePoint)
    (symmetricG : MetricFieldSymmetric g) (symmetricH : MetricFieldSymmetric h)
    (regularG : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (regularH : ∀ a b, ContDiffAt ℝ 2 (fun x => h x a b) p)
    (nondegenerateG : (g p).det ≠ 0) (nondegenerateH : (h p).det ≠ 0)
    (equal : MetricTwoJetEqualAt g h p) :
    loweredConnectionCurvature g (leviCivitaCoefficients g) p =
      loweredConnectionCurvature h (leviCivitaCoefficients h) p := by
  have hH : c2MetricHessian g p symmetricG regularG = c2MetricHessian h p symmetricH regularH := by
    apply Subtype.ext
    funext a b c d
    exact equal.2.2 a b c d
  funext a b c d
  rw [c2_general_coordinate_curvature_formula g p symmetricG regularG nondegenerateG,
    c2_general_coordinate_curvature_formula h p symmetricH regularH nondegenerateH, hH]
  simp only [leviCivita_metric_twojet_congr g h p equal, lowerChristoffel_metric_twojet_congr g h p equal]

#print axioms lowerChristoffel_metric_twojet_congr
#print axioms leviCivita_metric_twojet_congr
#print axioms c2_general_curvature_twojet_congr
end
end AASCSemanticExhaustion
