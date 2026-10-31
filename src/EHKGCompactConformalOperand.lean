import EHKGLocalSmoothGerm
import EHKGUniformCone
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! A compact original EH operand with an exact secant-squared local metric.
Compact localization removes the remote trigonometric singularities and gives
a uniform strict admission margin. No causal-domain or evolution certificate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology BigOperators
namespace AASCKleinGordon.CurvedKG

def conformalSeed (nu : ℝ) (p : CoordinatePoint) : ℝ := Real.tan (nu * p 0) ^ 2

def conformalSafeSet (nu : ℝ) : Set CoordinatePoint := {p | Real.cos (nu * p 0) ≠ 0}

theorem conformal_safe_open (nu : ℝ) : IsOpen (conformalSafeSet nu) := by
  change IsOpen ((fun p : CoordinatePoint => Real.cos (nu * p 0)) ⁻¹' {x : ℝ | x ≠ 0})
  exact isOpen_ne.preimage (by fun_prop)

theorem conformal_seed_smooth (nu : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (conformalSeed nu) (conformalSafeSet nu) := by
  apply (conformal_safe_open nu).contDiffOn_iff.mpr
  intro p hp
  have linear : ContDiff ℝ (⊤ : ℕ∞) (fun x : CoordinatePoint => nu * x 0) := by fun_prop
  have tanSmooth : ContDiffAt ℝ (⊤ : ℕ∞) Real.tan (nu * p 0) := Real.contDiffAt_tan.mpr hp
  exact (tanSmooth.comp p linear.contDiffAt).pow 2

theorem conformal_profile_exists (nu : ℝ) :
    ∃ h : ScalarSourceProbe (⊤ : Opens CoordinatePoint),
      (h : CoordinatePoint → ℝ) =ᶠ[𝓝 0] conformalSeed nu ∧
        ∀ p, |h p| ≤ (1 : ℝ) / 32 := by
  have safeZero : (0 : CoordinatePoint) ∈ conformalSafeSet nu := by
    simp [conformalSafeSet]
  have seedZero : conformalSeed nu 0 = 0 := by simp [conformalSeed]
  obtain ⟨h, near, bound⟩ := exists_compact_bounded_smooth_germ (conformalSeed nu) (conformalSafeSet nu)
    (conformal_safe_open nu) safeZero (conformal_seed_smooth nu) seedZero
    ((1 : ℝ) / 16) (by norm_num)
  refine ⟨h, near, fun p => ?_⟩
  convert bound p using 1 <;> norm_num

def conformalProfile (nu : ℝ) : ScalarSourceProbe (⊤ : Opens CoordinatePoint) :=
  Classical.choose (conformal_profile_exists nu)

theorem conformal_profile_germ (nu : ℝ) :
    (conformalProfile nu : CoordinatePoint → ℝ) =ᶠ[𝓝 0] conformalSeed nu :=
  (Classical.choose_spec (conformal_profile_exists nu)).1

theorem conformal_profile_bound (nu : ℝ) (p : CoordinatePoint) :
    |conformalProfile nu p| ≤ (1 : ℝ) / 32 :=
  (Classical.choose_spec (conformal_profile_exists nu)).2 p

def conformalOperand (nu : ℝ) : MetricSourceProbe (⊤ : Opens CoordinatePoint) :=
  -(sourceTestInsertion 0 (conformalProfile nu)) +
    sourceTestInsertion 4 (conformalProfile nu) +
    sourceTestInsertion 7 (conformalProfile nu) +
    sourceTestInsertion 9 (conformalProfile nu)

theorem conformal_operand_encoding (nu : ℝ) (p : CoordinatePoint) :
    tensorEncode (conformalOperand nu p) = conformalProfile nu p • metric := by
  have component (i : Fin 10) : conformalOperand nu p i =
      -(if i = 0 then conformalProfile nu p else 0) +
        (if i = 4 then conformalProfile nu p else 0) +
        (if i = 7 then conformalProfile nu p else 0) +
        (if i = 9 then conformalProfile nu p else 0) := by
    change -((sourceCoordinateInsertion 0) (conformalProfile nu p) i) +
      (sourceCoordinateInsertion 4) (conformalProfile nu p) i +
      (sourceCoordinateInsertion 7) (conformalProfile nu p) i +
      (sourceCoordinateInsertion 9) (conformalProfile nu p) i = _
    fin_cases i <;> simp [sourceCoordinateInsertion]
  funext i j
  fin_cases i <;> fin_cases j <;> simp [tensorEncode, component, metric, Matrix.diagonal_apply]

theorem conformal_operand_admitted (nu : ℝ) :
    conformalOperand nu ∈ wickOriginalMetricNeighborhood (⊤ : Opens CoordinatePoint) := by
  intro i j
  have bound : ‖wickNativeBoundedEntry (⊤ : Opens CoordinatePoint) i j (conformalOperand nu)‖ ≤
      (1 : ℝ) / 32 := by
    apply (BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1 / 32)).mpr
    intro p
    rw [wick_native_bounded_entry_apply, conformal_operand_encoding]
    fin_cases i <;> fin_cases j <;>
      simpa [metric, Matrix.diagonal_apply, Real.norm_eq_abs] using conformal_profile_bound nu p
  exact bound.trans_lt (by norm_num)

def conformalMetricFactor (nu : ℝ) (p : CoordinatePoint) : ℝ := 1 + conformalProfile nu p

theorem conformal_metric_factor_positive (nu : ℝ) (p : CoordinatePoint) :
    0 < conformalMetricFactor nu p := by
  have lower := (abs_le.mp (conformal_profile_bound nu p)).1
  dsimp [conformalMetricFactor]
  linarith

theorem conformal_operand_actual_metric (nu : ℝ) (p : CoordinatePoint) :
    originalEHActMetric (conformalOperand nu) p = conformalMetricFactor nu p • metric := by
  funext i j
  change wickNativeFlatMetric p i j + tensorEncode (conformalOperand nu p) i j = _
  rw [original_eh_native_flat_value, conformal_operand_encoding]
  change metric i j + conformalProfile nu p * metric i j =
    (1 + conformalProfile nu p) * metric i j
  ring

theorem conformal_seed_secant (nu : ℝ) (p : CoordinatePoint)
    (safe : p ∈ conformalSafeSet nu) :
    1 + conformalSeed nu p = (Real.cos (nu * p 0))⁻¹ ^ 2 := by
  have trig := Real.sin_sq_add_cos_sq (nu * p 0)
  dsimp [conformalSeed]
  rw [Real.tan_eq_sin_div_cos]
  dsimp [conformalSafeSet] at safe
  field_simp
  nlinarith

theorem conformal_operand_secant_germ (nu : ℝ) :
    originalEHActMetric (conformalOperand nu) =ᶠ[𝓝 0]
      (fun p => (Real.cos (nu * p 0))⁻¹ ^ 2 • metric) := by
  have safeZero : (0 : CoordinatePoint) ∈ conformalSafeSet nu := by simp [conformalSafeSet]
  filter_upwards [conformal_profile_germ nu, (conformal_safe_open nu).mem_nhds safeZero] with p hp hs
  rw [conformal_operand_actual_metric]
  change (1 + conformalProfile nu p) • metric = _
  rw [hp, conformal_seed_secant nu p hs]

theorem quadratic_scalar_multiple (r : ℝ) (M : Tensor2) (v : CoordinatePoint) :
    wickMatrixQuadratic (r • M) v = r * wickMatrixQuadratic M v := by
  simp only [wickMatrixQuadratic, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change v i * (r * M i j) * v j = _
  ring

theorem conformal_operand_causal_tangent_iff (nu : ℝ) (p v : CoordinatePoint) :
    wickMatrixQuadratic (originalEHActMetric (conformalOperand nu) p) v ≤ 0 ↔
      wickMatrixQuadratic metric v ≤ 0 := by
  rw [conformal_operand_actual_metric, quadratic_scalar_multiple]
  have positive := conformal_metric_factor_positive nu p
  constructor
  · intro h
    nlinarith
  · exact mul_nonpos_of_nonneg_of_nonpos positive.le

end AASCKleinGordon.CurvedKG
