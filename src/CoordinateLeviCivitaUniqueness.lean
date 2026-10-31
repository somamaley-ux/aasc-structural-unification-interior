import CoordinateLeviCivita

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

def lowerConnection (g : MetricField) (Γ : ConnectionCoefficients)
    (x : CoordinatePoint) (a b c : Fin 4) : ℝ :=
  ∑ d : Fin 4, g x a d * Γ x d b c

theorem lowerConnection_torsion_free (g : MetricField) (Γ : ConnectionCoefficients)
    (torsion : CoordinateTorsionFree Γ) (x : CoordinatePoint) (a b c : Fin 4) :
    lowerConnection g Γ x a b c = lowerConnection g Γ x a c b := by
  unfold lowerConnection
  simp_rw [torsion x _ b c]

theorem compatible_connection_lowered (g : MetricField) (Γ : ConnectionCoefficients)
    (symmetric : MetricFieldSymmetric g) (x : CoordinatePoint)
    (compatible : CoordinateMetricCompatible g Γ x) (a b c : Fin 4) :
    metricPartial g x a b c = lowerConnection g Γ x b c a + lowerConnection g Γ x a c b := by
  rw [compatible a b c]
  unfold lowerConnection
  congr 1
  · apply Finset.sum_congr rfl
    intro d _
    rw [symmetric x d b]
    ring
  · apply Finset.sum_congr rfl
    intro d _
    ring

theorem compatible_torsion_free_koszul (g : MetricField) (Γ : ConnectionCoefficients)
    (symmetric : MetricFieldSymmetric g) (torsion : CoordinateTorsionFree Γ)
    (x : CoordinatePoint) (compatible : CoordinateMetricCompatible g Γ x)
    (a b c : Fin 4) : lowerConnection g Γ x a b c = lowerChristoffel g x a b c := by
  unfold lowerChristoffel
  rw [compatible_connection_lowered g Γ symmetric x compatible a c b,
    compatible_connection_lowered g Γ symmetric x compatible a b c,
    compatible_connection_lowered g Γ symmetric x compatible b c a]
  linarith [lowerConnection_torsion_free g Γ torsion x c b a,
    lowerConnection_torsion_free g Γ torsion x b c a,
    lowerConnection_torsion_free g Γ torsion x a c b]

theorem raise_lower_connection (g : MetricField) (Γ : ConnectionCoefficients)
    (x : CoordinatePoint) (nondegenerate : (g x).det ≠ 0) (a b c : Fin 4) :
    (∑ d : Fin 4, (g x)⁻¹ a d * lowerConnection g Γ x d b c) = Γ x a b c := by
  have hi : (g x)⁻¹ * g x = 1 :=
    Matrix.nonsing_inv_mul (g x) (isUnit_iff_ne_zero.mpr nondegenerate)
  simp only [lowerConnection, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  change (∑ e : Fin 4, ((g x)⁻¹ * g x) a e * Γ x e b c) = _
  rw [hi]
  simp [Matrix.one_apply, ite_mul]

theorem coordinate_leviCivita_unique (g : MetricField) (Γ : ConnectionCoefficients)
    (symmetric : MetricFieldSymmetric g) (torsion : CoordinateTorsionFree Γ)
    (x : CoordinatePoint) (nondegenerate : (g x).det ≠ 0)
    (compatible : CoordinateMetricCompatible g Γ x) (a b c : Fin 4) :
    Γ x a b c = leviCivitaCoefficients g x a b c := by
  rw [← raise_lower_connection g Γ x nondegenerate a b c]
  unfold leviCivitaCoefficients
  simp_rw [compatible_torsion_free_koszul g Γ symmetric torsion x compatible]

#print axioms lowerConnection_torsion_free
#print axioms compatible_connection_lowered
#print axioms compatible_torsion_free_koszul
#print axioms raise_lower_connection
#print axioms coordinate_leviCivita_unique
end
end AASCSemanticExhaustion
