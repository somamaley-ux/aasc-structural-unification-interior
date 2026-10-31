import EHKGAllCompactCauchy
import NativeRealClockDensityDerivative

/-! The inherited scalar density evaluated at the very same original EH
metric. This is an actual determinant/inverse calculation, with its mass
argument interpreted as mass squared. It is not a coupled source theorem. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology BigOperators
namespace AASCKleinGordon.CurvedKG

theorem time_conformal_determinant (A : ℝ → ℝ) (p : CoordinatePoint) :
    (timeConformalMetric A p).det = -(A (p 0)) ^ 8 := by
  rw [timeConformalMetric, Matrix.det_smul]
  norm_num [metric, Matrix.det_diagonal, Fin.prod_univ_succ]
  ring

theorem time_conformal_volume (A : ℝ → ℝ) (p : CoordinatePoint) :
    nativeRealClockVolume (timeConformalMetric A p) = (A (p 0)) ^ 4 := by
  rw [nativeRealClockVolume, time_conformal_determinant, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ (A (p 0)) ^ 8)]
  rw [show (A (p 0)) ^ 8 = ((A (p 0)) ^ 4) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (A (p 0)) ^ 4)]

def sameEHScalarDensity (a : Parameters) (u : CoordinatePoint → ℝ) (p : CoordinatePoint) : ℝ :=
  nativeRealClockDensity (originalEHActMetric (conformalOperand (conformalFrequency a)) p)
    (scalarPartial u p) (u p) ((massWaveNumber a) ^ 2)

theorem time_conformal_scalar_density (A : ℝ → ℝ) (p : CoordinatePoint)
    (nonzero : A (p 0) ≠ 0) (v : Fin 4 → ℝ) (phi mu2 : ℝ) :
    nativeRealClockDensity (timeConformalMetric A p) v phi mu2 =
      (1 / 2 : ℝ) * ((A (p 0)) ^ 2 * (v 0 ^ 2 - v 1 ^ 2 - v 2 ^ 2 - v 3 ^ 2) -
        mu2 * (A (p 0)) ^ 4 * phi ^ 2) := by
  rw [nativeRealClockDensity, time_conformal_volume, time_conformal_inverse A p nonzero]
  have contraction : (∑ i : Fin 4, ∑ j : Fin 4, metric i j * v i * v j) =
      -v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by
    simp_rw [mul_assoc]
    rw [canonical_metric_contraction_diagonal, Fin.sum_univ_four]
    change (-1) * (v 0 * v 0) + 1 * (v 1 * v 1) +
      1 * (v 2 * v 2) + 1 * (v 3 * v 3) = _
    ring
  have factor : (∑ i : Fin 4, ∑ j : Fin 4,
      (((A (p 0)) ^ 2)⁻¹ • metric) i j * v i * v j) =
      ((A (p 0)) ^ 2)⁻¹ * (∑ i : Fin 4, ∑ j : Fin 4, metric i j * v i * v j) := by
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [factor, contraction]
  field_simp [nonzero]
  <;> ring

theorem protected_same_eh_scalar_density (a : Parameters) (u : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (inside : p ∈ protectedDiamond (conformalFrequency a)) :
    sameEHScalarDensity a u p =
      (1 / 2 : ℝ) * ((secantScale (conformalFrequency a) (p 0)) ^ 2 *
        (scalarPartial u p 0 ^ 2 - scalarPartial u p 1 ^ 2 -
          scalarPartial u p 2 ^ 2 - scalarPartial u p 3 ^ 2) -
        (massWaveNumber a) ^ 2 * (secantScale (conformalFrequency a) (p 0)) ^ 4 * u p ^ 2) := by
  rw [sameEHScalarDensity, protected_metric_identity _ _ (protected_diamond_subset_ball _ inside)]
  have safe : secantScale (conformalFrequency a) (p 0) ≠ 0 :=
    inv_ne_zero (ne_of_gt (protected_cosine_positive _ _ (protected_diamond_subset_ball _ inside)))
  exact time_conformal_scalar_density (secantScale (conformalFrequency a)) p safe
    (scalarPartial u p) (u p) ((massWaveNumber a) ^ 2)

end AASCKleinGordon.CurvedKG
