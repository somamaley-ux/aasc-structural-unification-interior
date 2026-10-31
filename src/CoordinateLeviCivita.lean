import SmoothMetricJetRealization

/-!
The coordinate Levi-Civita coefficients are constructed from actual first
Frechet derivatives and the matrix inverse. Torsion and metric compatibility
are checked from symmetry and nonsingularity, not received as certificate fields.
The ambient chart is the open finite-dimensional coordinate receiver.
-/
namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

abbrev CoordinatePoint := Fin 4 → ℝ
abbrev MetricField := CoordinatePoint → Tensor2
abbrev ConnectionCoefficients := CoordinatePoint → Fin 4 → Fin 4 → Fin 4 → ℝ

def metricPartial (g : MetricField) (x : CoordinatePoint) (a b c : Fin 4) : ℝ :=
  fderiv ℝ (fun y => g y a b) x (Pi.single c 1)

def lowerChristoffel (g : MetricField) (x : CoordinatePoint) (a b c : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * (metricPartial g x a c b + metricPartial g x a b c - metricPartial g x b c a)

def leviCivitaCoefficients (g : MetricField) : ConnectionCoefficients := fun x a b c =>
  ∑ d : Fin 4, (g x)⁻¹ a d * lowerChristoffel g x d b c

def MetricFieldSymmetric (g : MetricField) : Prop := ∀ x a b, g x a b = g x b a

def CoordinateTorsionFree (Γ : ConnectionCoefficients) : Prop :=
  ∀ x a b c, Γ x a b c = Γ x a c b

def CoordinateMetricCompatible (g : MetricField) (Γ : ConnectionCoefficients)
    (x : CoordinatePoint) : Prop := ∀ a b c,
  metricPartial g x a b c =
    (∑ d : Fin 4, Γ x d c a * g x d b) + (∑ d : Fin 4, Γ x d c b * g x a d)

theorem metricPartial_symmetric (g : MetricField) (symmetric : MetricFieldSymmetric g)
    (x : CoordinatePoint) (a b c : Fin 4) : metricPartial g x a b c = metricPartial g x b a c := by
  unfold metricPartial
  have h : (fun y => g y a b) = (fun y => g y b a) := funext (fun y => symmetric y a b)
  rw [h]

theorem lowerChristoffel_torsion_free (g : MetricField) (symmetric : MetricFieldSymmetric g)
    (x : CoordinatePoint) (a b c : Fin 4) : lowerChristoffel g x a b c = lowerChristoffel g x a c b := by
  unfold lowerChristoffel
  rw [metricPartial_symmetric g symmetric x c b a]
  ring

theorem leviCivita_torsion_free (g : MetricField) (symmetric : MetricFieldSymmetric g) :
    CoordinateTorsionFree (leviCivitaCoefficients g) := by
  intro x a b c
  unfold leviCivitaCoefficients
  simp_rw [lowerChristoffel_torsion_free g symmetric x _ b c]

theorem leviCivita_lowering (g : MetricField) (x : CoordinatePoint)
    (nondegenerate : (g x).det ≠ 0) (a b c : Fin 4) :
    (∑ d : Fin 4, g x a d * leviCivitaCoefficients g x d b c) = lowerChristoffel g x a b c := by
  have hi : g x * (g x)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv (g x) (isUnit_iff_ne_zero.mpr nondegenerate)
  simp only [leviCivitaCoefficients, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  change (∑ e : Fin 4, (g x * (g x)⁻¹) a e * lowerChristoffel g x e b c) = _
  rw [hi]
  simp [Matrix.one_apply, ite_mul]

theorem lowerChristoffel_metric_compatibility (g : MetricField)
    (symmetric : MetricFieldSymmetric g) (x : CoordinatePoint) (a b c : Fin 4) :
    metricPartial g x a b c = lowerChristoffel g x a c b + lowerChristoffel g x b c a := by
  unfold lowerChristoffel
  rw [metricPartial_symmetric g symmetric x b a c,
    metricPartial_symmetric g symmetric x c b a,
    metricPartial_symmetric g symmetric x c a b]
  ring

theorem leviCivita_metric_compatible (g : MetricField) (symmetric : MetricFieldSymmetric g)
    (x : CoordinatePoint) (nondegenerate : (g x).det ≠ 0) :
    CoordinateMetricCompatible g (leviCivitaCoefficients g) x := by
  intro a b c
  have left : (∑ d : Fin 4, leviCivitaCoefficients g x d c a * g x d b) =
      lowerChristoffel g x b c a := by
    calc
      _ = ∑ d : Fin 4, g x b d * leviCivitaCoefficients g x d c a := by
        apply Finset.sum_congr rfl
        intro d _
        rw [symmetric x d b]
        ring
      _ = _ := leviCivita_lowering g x nondegenerate b c a
  have right : (∑ d : Fin 4, leviCivitaCoefficients g x d c b * g x a d) =
      lowerChristoffel g x a c b := by
    simpa only [mul_comm] using leviCivita_lowering g x nondegenerate a c b
  rw [left, right]
  rw [lowerChristoffel_metric_compatibility g symmetric x a b c]
  ring

#print axioms metricPartial_symmetric
#print axioms lowerChristoffel_torsion_free
#print axioms leviCivita_torsion_free
#print axioms leviCivita_lowering
#print axioms lowerChristoffel_metric_compatibility
#print axioms leviCivita_metric_compatible
end
end AASCSemanticExhaustion
