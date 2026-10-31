import SKGTotalActionSource
import OriginalEHGeometricNaturality

/-! Complete compact-test stationarity is equivalent to the actual sourced
Einstein equation. This is a conditional variational equation theorem,
not an existence theorem for a coupled Einstein--KG development. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

def sameEinsteinTensor (a : Parameters) (Lambda : ℝ) (p : CoordinatePoint) : Tensor2 :=
  coordinateRicci (sourceMetric a) p -
    (coordinateScalarCurvature (sourceMetric a) p / 2) • sourceMetric a p + Lambda • sourceMetric a p

theorem same_eh_component_density (a : Parameters) (kappa Lambda : ℝ) (p : CoordinatePoint)
    (i : Fin 10) : ehComputedSourceDensity kappa Lambda (sourceMetric a) i p =
      sourceDensityCoordinates (raisedSourceTensorDensity (sourceMetric a)
        (originalEHGeometricResponse kappa Lambda (sourceMetric a))) i p := by
  unfold sourceDensityCoordinates
  rw [eh_original_geometric_tensor_density kappa Lambda (sourceMetric a)
    (source_metric_symmetric a) p (source_metric_determinant_negative a p)]
  fin_cases i <;> rfl

theorem same_total_density_geometric_balance (a : Parameters) (kappa Lambda : ℝ)
    (u : CoordinatePoint → ℝ) (p : CoordinatePoint) (i : Fin 10) :
    totalActualDensity a kappa Lambda u i p =
      (metric (sourceSymmetricPair i).1 (sourceSymmetricPair i).1 *
        metric (sourceSymmetricPair i).2 (sourceSymmetricPair i).2) *
      tensorDecode (originalEHGeometricResponse kappa Lambda (sourceMetric a) p + sameSourceStress a u p) i := by
  unfold totalActualDensity actualSourceDensityCoordinates
  rw [same_eh_component_density]
  change raisedSourceTensorDensity (sourceMetric a)
      (originalEHGeometricResponse kappa Lambda (sourceMetric a)) p (sourceSymmetricPair i).1 (sourceSymmetricPair i).2 +
    raisedSourceTensorDensity (sourceMetric a) (sameSourceStress a u) p (sourceSymmetricPair i).1 (sourceSymmetricPair i).2 = _
  rw [same_source_raised_density, same_source_raised_density]
  fin_cases i <;> simp only [sourceSymmetricPair, tensorDecode, Matrix.add_apply] <;> ring

theorem same_total_density_zero_iff_tensor_balance (a : Parameters) (kappa Lambda : ℝ)
    (coupling : kappa ≠ 0) (u : CoordinatePoint → ℝ) (p : CoordinatePoint) :
    (∀ i : Fin 10, totalActualDensity a kappa Lambda u i p = 0) ↔
      originalEHGeometricResponse kappa Lambda (sourceMetric a) p + sameSourceStress a u p = 0 := by
  let Q := originalEHGeometricResponse kappa Lambda (sourceMetric a) p + sameSourceStress a u p
  have geometricSymmetry (i j : Fin 4) :
      originalEHGeometricResponse kappa Lambda (sourceMetric a) p i j =
        originalEHGeometricResponse kappa Lambda (sourceMetric a) p j i := by
    rw [eh_original_geometric_tensor_identified kappa Lambda coupling (sourceMetric a) p
      (source_metric_determinant_negative a p)]
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    rw [eh_actual_ricci_symmetric (sourceMetric a) (source_metric_symmetric a)
      (source_metric_smooth a) p (source_metric_nondegenerate a p) i j,
      source_metric_symmetric a p i j]
  have symmetry : ∀ i j, Q i j = Q j i := by
    intro i j
    change originalEHGeometricResponse kappa Lambda (sourceMetric a) p i j + sameSourceStress a u p i j = _
    rw [geometricSymmetry i j,
      same_source_stress_symmetric a u p i j]
    rfl
  constructor
  · intro zero
    have decoded : tensorDecode Q = 0 := by
      funext i
      have entry := zero i
      rw [same_total_density_geometric_balance] at entry
      have signNonzero : (metric (sourceSymmetricPair i).1 (sourceSymmetricPair i).1 *
          metric (sourceSymmetricPair i).2 (sourceSymmetricPair i).2) ≠ 0 := by
        have diagonalNonzero (j : Fin 4) : metric j j ≠ 0 := by
          fin_cases j
          · change (-1 : ℝ) ≠ 0
            norm_num
          all_goals change (1 : ℝ) ≠ 0
          all_goals norm_num
        exact mul_ne_zero (diagonalNonzero _) (diagonalNonzero _)
      exact (mul_eq_zero.mp entry).resolve_left signNonzero
    have encoded := tensor_encode_decode Q symmetry
    rw [decoded] at encoded
    have encodeZero : tensorEncode (0 : Fin 10 → ℝ) = (0 : Tensor2) := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [encodeZero] at encoded
    exact encoded.symm
  · intro balance i
    rw [same_total_density_geometric_balance, balance]
    fin_cases i <;> simp [tensorDecode]

theorem same_geometric_balance_iff_sourced_einstein (a : Parameters) (kappa Lambda : ℝ)
    (coupling : kappa ≠ 0) (u : CoordinatePoint → ℝ) (p : CoordinatePoint) :
    originalEHGeometricResponse kappa Lambda (sourceMetric a) p + sameSourceStress a u p = 0 ↔
      sameEinsteinTensor a Lambda p = kappa • sameSourceStress a u p := by
  rw [eh_original_geometric_tensor_identified kappa Lambda coupling (sourceMetric a) p
    (source_metric_determinant_negative a p)]
  change -(1 / kappa) • sameEinsteinTensor a Lambda p + sameSourceStress a u p = 0 ↔ _
  constructor
  · intro balance
    ext i j
    have entry := congrArg (fun M : Tensor2 => M i j) balance
    change -(1 / kappa) * sameEinsteinTensor a Lambda p i j + sameSourceStress a u p i j = 0 at entry
    change sameEinsteinTensor a Lambda p i j = kappa * sameSourceStress a u p i j
    field_simp [coupling] at entry
    linarith
  · intro equation
    ext i j
    have entry := congrArg (fun M : Tensor2 => M i j) equation
    change sameEinsteinTensor a Lambda p i j = kappa * sameSourceStress a u p i j at entry
    change -(1 / kappa) * sameEinsteinTensor a Lambda p i j + sameSourceStress a u p i j = 0
    rw [entry]
    field_simp [coupling]
    <;> ring

theorem actual_total_metric_stationarity_iff_sourced_einstein (a : Parameters)
    (kappa Lambda : ℝ) (coupling : kappa ≠ 0) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ (⊤ : ℕ∞) u) :
    SameTotalMetricStationary a kappa Lambda u ↔
      ∀ p ∈ sourceDomain a, sameEinsteinTensor a Lambda p = kappa • sameSourceStress a u p := by
  rw [total_stationary_iff_pointwise_density a kappa Lambda coupling u regular]
  exact forall₂_congr (fun p _ => (same_total_density_zero_iff_tensor_balance a kappa Lambda coupling u p).trans
    (same_geometric_balance_iff_sourced_einstein a kappa Lambda coupling u p))

end AASCKleinGordon.SameActionSource
