import NormalizedCubicMetricTransport
import NormalizedLorentzMetricTransport

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0

def C2NormalizedMetricGerm (g : MetricField) : Prop :=
  MetricFieldSymmetric g ∧ (∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) 0) ∧
    g 0 = metric ∧ ∀ a b, fderiv ℝ (fun x => g x a b) 0 = 0

theorem c2_scalarSecondPartial_full_second_derivative (f : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (regular : ContDiffAt ℝ 2 f p) (c d : Fin 4) :
    scalarSecondPartial f p c d =
      fderiv ℝ (fderiv ℝ f) p (Pi.single d 1) (Pi.single c 1) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (regular.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold scalarSecondPartial scalarPartial
  rw [fderiv_clm_apply hdf (differentiableAt_const (Pi.single c (1 : ℝ)))]
  simp

theorem c2_scalarSecondPartial_symmetric (f : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (regular : ContDiffAt ℝ 2 f p) (c d : Fin 4) :
    scalarSecondPartial f p c d = scalarSecondPartial f p d c := by
  rw [c2_scalarSecondPartial_full_second_derivative f p regular,
    c2_scalarSecondPartial_full_second_derivative f p regular]
  exact (regular.isSymmSndFDerivAt (by norm_num)) (Pi.single d 1) (Pi.single c 1)

def c2MetricHessian (g : MetricField) (p : CoordinatePoint)
    (symmetric : MetricFieldSymmetric g)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p) : metricHessianSpace where
  val a b c d := scalarSecondPartial (fun x => g x a b) p c d
  property := by
    constructor
    · intro a b c d
      change scalarSecondPartial (fun x => g x a b) p c d =
        scalarSecondPartial (fun x => g x b a) p c d
      have heq : (fun x => g x a b) = (fun x => g x b a) := funext (fun x => symmetric x a b)
      rw [heq]
    · intro a b c d
      exact c2_scalarSecondPartial_symmetric _ p (regular a b) c d

theorem c2_normalized_metric_matches_receiver (g : MetricField)
    (germ : C2NormalizedMetricGerm g) :
    MetricTwoJetEqualAt g (hessianMetricPolynomial (c2MetricHessian g 0 germ.1 germ.2.1)) 0 := by
  refine ⟨germ.2.2.1.trans (hessianMetricPolynomial_zero _).symm, ?_, ?_⟩
  · intro a b
    rw [germ.2.2.2 a b, hessianMetricPolynomial_first_zero]
  · intro a b c d
    rw [hessian_metric_scalarSecond]
    rfl

theorem hessianMetricPolynomial_c2_normalized (H : metricHessianSpace) :
    C2NormalizedMetricGerm (hessianMetricPolynomial H) := by
  refine ⟨hessianMetricPolynomial_symmetric H, ?_, hessianMetricPolynomial_zero H,
    hessianMetricPolynomial_first_zero H⟩
  intro a b
  exact (hessianMetricPolynomial_smooth H a b).contDiffAt.of_le (by simp)

def c2NormalizedMetricJetCurvature (g : MetricField) (germ : C2NormalizedMetricGerm g) : curvatureSpace :=
  curvatureJetMap (c2MetricHessian g 0 germ.1 germ.2.1)

theorem c2NormalizedMetricJetCurvature_receiver (H : metricHessianSpace) :
    c2NormalizedMetricJetCurvature (hessianMetricPolynomial H) (hessianMetricPolynomial_c2_normalized H) =
      curvatureJetMap H := by
  apply congrArg curvatureJetMap
  apply Subtype.ext
  funext a b c d
  exact hessian_metric_scalarSecond H a b c d

/-- The arbitrary-response exhaustion extends to every C² normalized metric
germ. The original core need only control the analytic polynomial test class. -/
theorem metric_response_c2_normalized_germ_exhaustion (E : MetricFieldResponse)
    (core : MetricFirstResponseCore E) :
    ∃! coefficients : ℝ × ℝ × ℝ, ∀ g : MetricField, ∀ germ : C2NormalizedMetricGerm g,
      E g 0 = coefficients.1 • ricciResponse (c2NormalizedMetricJetCurvature g germ) +
        coefficients.2.1 • scalarMetricResponse (c2NormalizedMetricJetCurvature g germ) +
          coefficients.2.2 • metric := by
  obtain ⟨coefficients, h, unique⟩ := metric_field_response_jet_exhaustion E core
  refine ⟨coefficients, ?_, ?_⟩
  · intro g germ
    rw [core.2.1 g _ 0 (c2_normalized_metric_matches_receiver g germ)]
    exact h (c2MetricHessian g 0 germ.1 germ.2.1)
  · intro other ho
    apply unique other
    intro H
    have hh := ho (hessianMetricPolynomial H) (hessianMetricPolynomial_c2_normalized H)
    simpa only [c2NormalizedMetricJetCurvature_receiver] using hh

#print axioms c2_scalarSecondPartial_full_second_derivative
#print axioms c2_scalarSecondPartial_symmetric
#print axioms c2_normalized_metric_matches_receiver
#print axioms hessianMetricPolynomial_c2_normalized
#print axioms c2NormalizedMetricJetCurvature_receiver
#print axioms metric_response_c2_normalized_germ_exhaustion
end
end AASCSemanticExhaustion
