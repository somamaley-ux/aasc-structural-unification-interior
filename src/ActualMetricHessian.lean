import CoordinateMetricNaturality
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0

theorem scalarSecondPartial_full_second_derivative (f : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (smooth : ContDiffAt ℝ ⊤ f p) (c d : Fin 4) :
    scalarSecondPartial f p c d =
      fderiv ℝ (fderiv ℝ f) p (Pi.single d 1) (Pi.single c 1) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (smooth.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  unfold scalarSecondPartial scalarPartial
  rw [fderiv_clm_apply hdf (differentiableAt_const (Pi.single c (1 : ℝ)))]
  simp

theorem scalarSecondPartial_symmetric (f : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (smooth : ContDiffAt ℝ ⊤ f p) (c d : Fin 4) :
    scalarSecondPartial f p c d = scalarSecondPartial f p d c := by
  rw [scalarSecondPartial_full_second_derivative f p smooth,
    scalarSecondPartial_full_second_derivative f p smooth]
  exact (smooth.isSymmSndFDerivAt (by simp)) (Pi.single d 1) (Pi.single c 1)

def actualMetricHessian (g : MetricField) (p : CoordinatePoint)
    (symmetric : MetricFieldSymmetric g)
    (smooth : ∀ a b, ContDiffAt ℝ ⊤ (fun x => g x a b) p) : metricHessianSpace where
  val a b c d := scalarSecondPartial (fun x => g x a b) p c d
  property := by
    constructor
    · intro a b c d
      change scalarSecondPartial (fun x => g x a b) p c d =
        scalarSecondPartial (fun x => g x b a) p c d
      have heq : (fun x => g x a b) = (fun x => g x b a) := funext (fun x => symmetric x a b)
      rw [heq]
    · intro a b c d
      exact scalarSecondPartial_symmetric _ p (smooth a b) c d

theorem actualMetricHessian_component (g : MetricField) (p : CoordinatePoint)
    (symmetric : MetricFieldSymmetric g)
    (smooth : ∀ a b, ContDiffAt ℝ ⊤ (fun x => g x a b) p) (a b c d : Fin 4) :
    ((actualMetricHessian g p symmetric smooth : metricHessianSpace) : Tensor4) a b c d =
      scalarSecondPartial (fun x => g x a b) p c d := rfl

theorem normalized_metric_matches_hessian_receiver (g : MetricField)
    (symmetric : MetricFieldSymmetric g)
    (smooth : ∀ a b, ContDiffAt ℝ ⊤ (fun x => g x a b) 0)
    (value : g 0 = metric) (first : ∀ a b, fderiv ℝ (fun x => g x a b) 0 = 0) :
    MetricTwoJetEqualAt g (hessianMetricPolynomial (actualMetricHessian g 0 symmetric smooth)) 0 := by
  refine ⟨value.trans (hessianMetricPolynomial_zero _).symm, ?_, ?_⟩
  · intro a b
    rw [first a b, hessianMetricPolynomial_first_zero]
  · intro a b c d
    change _ = fderiv ℝ (fun x => fderiv ℝ
      (fun y => hessianMetricPolynomial (actualMetricHessian g 0 symmetric smooth) y a b) x
        (Pi.single c 1)) 0 (Pi.single d 1)
    rw [hessianMetricPolynomial_second]
    rfl

theorem metric_response_normalized_jet_factorization (E : MetricFieldResponse)
    (localOrder : MetricTwoJetLocal E) (g : MetricField)
    (symmetric : MetricFieldSymmetric g)
    (smooth : ∀ a b, ContDiffAt ℝ ⊤ (fun x => g x a b) 0)
    (value : g 0 = metric) (first : ∀ a b, fderiv ℝ (fun x => g x a b) 0 = 0) :
    E g 0 = E (hessianMetricPolynomial (actualMetricHessian g 0 symmetric smooth)) 0 :=
  localOrder g _ 0 (normalized_metric_matches_hessian_receiver g symmetric smooth value first)

#print axioms scalarSecondPartial_full_second_derivative
#print axioms scalarSecondPartial_symmetric
#print axioms actualMetricHessian_component
#print axioms normalized_metric_matches_hessian_receiver
#print axioms metric_response_normalized_jet_factorization
end
end AASCSemanticExhaustion
