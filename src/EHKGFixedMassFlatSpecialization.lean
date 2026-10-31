import EHKGCompactFinitePropagation

/-! Independent H=0 specialization with the original positive physical mass.
It is not the curvature-to-zero limit of the mass-tuned secant construction.
The solution is exactly the retained full Fourier family at parameter a. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped SchwartzMap Topology
namespace AASCKleinGordon.CurvedKG

theorem zero_eh_metric_is_constant_conformal :
    originalEHActMetric (0 : MetricSourceProbe (⊤ : Opens CoordinatePoint)) = timeConformalMetric (fun _ => 1) := by
  funext p
  ext i j
  change wickNativeFlatMetric p i j + tensorEncode ((0 : MetricSourceProbe (⊤ : Opens CoordinatePoint)) p) i j = _
  rw [original_eh_native_flat_value]
  fin_cases i <;> fin_cases j <;> simp [timeConformalMetric, tensorEncode]

theorem zero_eh_operator_is_original_flat (mu2 : ℝ) (u : CoordinatePoint → ℝ) (p : CoordinatePoint) :
    scalarFieldWaveOperator (originalEHActMetric (0 : MetricSourceProbe (⊤ : Opens CoordinatePoint))) u p - mu2 * u p =
      -flatScalarResidual mu2 u p := by
  rw [zero_eh_metric_is_constant_conformal,
    time_conformal_scalar_wave_operator (fun _ => 1) p 0 (hasDerivAt_const _ 1) (by norm_num)]
  simp only [one_pow, inv_one, one_mul, zero_mul, zero_div, sub_zero, flatScalarResidual]
  ring

def compactFlatField (a : Parameters) (U : Opens KGSpatialSpace)
    (f h : TestFunction U ℝ (⊤ : ℕ∞)) : CoordinatePoint → ℝ :=
  flatCoordinateField a (compactCauchySchwartzCLM U f) (compactCauchySchwartzCLM U h) Complex.reCLM

theorem fixed_mass_flat_field_is_inherited_fourier (a : Parameters) (U : Opens KGSpatialSpace)
    (f h : TestFunction U ℝ (⊤ : ℕ∞)) (p : CoordinatePoint) :
    compactFlatField a U f h p = Complex.reCLM (fullFlatPosition a
      (compactCauchySchwartzCLM U f) (compactCauchySchwartzCLM U h) (p 0) (coordinateSpatialCLM p)) := rfl

theorem fixed_mass_flat_field_smooth (a : Parameters) (U : Opens KGSpatialSpace)
    (f h : TestFunction U ℝ (⊤ : ℕ∞)) : ContDiff ℝ (⊤ : ℕ∞) (compactFlatField a U f h) :=
  flat_coordinate_smooth _ _ _ _

theorem fixed_mass_flat_same_eh_equation (a : Parameters) (U : Opens KGSpatialSpace)
    (f h : TestFunction U ℝ (⊤ : ℕ∞)) (p : CoordinatePoint) :
    scalarFieldWaveOperator (originalEHActMetric (0 : MetricSourceProbe (⊤ : Opens CoordinatePoint)))
      (compactFlatField a U f h) p = (massWaveNumber a) ^ 2 * compactFlatField a U f h p := by
  apply sub_eq_zero.mp
  rw [zero_eh_operator_is_original_flat, compactFlatField, flat_coordinate_residual_zero, neg_zero]

theorem fixed_mass_flat_initial_position (a : Parameters) (U : Opens KGSpatialSpace)
    (f h : TestFunction U ℝ (⊤ : ℕ∞)) (x : KGSpatialSpace) : compactFlatField a U f h (centralLeafPoint x) = f x := by
  simp [compactFlatField, flatCoordinateField, central_leaf_time, central_leaf_space,
    full_flat_initial_position, compact_cauchy_schwartz_apply, coordinate_split_time]

theorem fixed_mass_flat_initial_velocity (a : Parameters) (U : Opens KGSpatialSpace)
    (f h : TestFunction U ℝ (⊤ : ℕ∞)) (x : KGSpatialSpace) :
    scalarPartial (compactFlatField a U f h) (centralLeafPoint x) 0 = h x := by
  rw [compactFlatField, flat_coordinate_time_partial]
  simp [flatCoordinateField, central_leaf_time, central_leaf_space, coordinate_split_time,
    full_flat_initial_position, compact_cauchy_schwartz_apply]

end AASCKleinGordon.CurvedKG
