import OccupiedMetricProfiles
import OriginalEHGeometricCore
import NativeActionClassicalSource
import ActualCompactSourceLie

/-! Original compact Lie observations of a bounded metric operand. The tests
and their standing are fixed before either the candidate or the original action
is evaluated. At a normalized occupied germ, agreement on these tests implies
classical covariant closure without giving the rival an action. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Filter MeasureTheory TopologicalSpace
open AASCSemanticExhaustion AASCKleinGordon
open AASCMetricityOriginalAssembly AASCMetricityLicensingConstruction
open AASCKleinGordon.CanonicalLicensing
open scoped Topology BigOperators ContDiff
namespace AASCOccupiedProfiles

variable {Ω : Opens CoordinatePoint}

abbrev operandLieTest (H : AdmittedOperand Ω) (X : CoordinateVectorProbe Ω) :
    MetricSourceProbe Ω :=
  compactMetricLieCLM Ω (originalEHActMetric H.val) (original_eh_act_metric_smooth H.val) X

/-- Whether this actual Lie probe is available is independent of its value. -/
theorem occupied_lie_probe_has_standing (a : Parameters) (s κ Λ : ℝ) (hk : κ ≠ 0)
    (H : AdmittedOperand Ω) (X : CoordinateVectorProbe Ω) :
    H ∈ currentOperand a Ω '' canonicalSafeUses (originalMetricTask a s Ω κ Λ) ∧
    ∀ᶠ t : ℝ in 𝓝 0, H.val + t • operandLieTest H X ∈ wickOriginalMetricNeighborhood Ω := by
  constructor
  · rw [original_safe_operand_image a s Ω κ Λ hk]
    trivial
  · exact original_eh_actual_act_curve_admitted H.val H.property _

/-- Equality of the restricted readings is exactly equality of the two weak
divergences, independently of how either continuous response is presented. -/
theorem compact_lie_readings_iff_same_divergence (g : MetricField)
    (smooth : SmoothCoordinateMetric g) (symmetric : MetricFieldSymmetric g)
    (V W : MetricSourceProbe Ω →L[ℝ] ℝ) :
    (∀ X, V (compactMetricLieCLM Ω g smooth X) = W (compactMetricLieCLM Ω g smooth X)) ↔
      constructedSourceDivergence Ω g smooth (representedMetricSource V) =
      constructedSourceDivergence Ω g smooth (representedMetricSource W) := by
  have wh := (constructed_source_ward_iff_divergence Ω g smooth symmetric W
    (constructedSourceDivergence Ω g smooth (representedMetricSource W))).mpr rfl
  have vh := constructed_source_ward_iff_divergence Ω g smooth symmetric V
    (constructedSourceDivergence Ω g smooth (representedMetricSource W))
  constructor
  · exact fun h => vh.mp (fun X => (h X).trans (wh X))
  · exact fun h X => (vh.mpr h X).trans (wh X).symm

abbrev operandOriginalReading (κ Λ : ℝ) (hk : κ ≠ 0) (H : AdmittedOperand Ω) :
    MetricSourceProbe Ω →L[ℝ] ℝ :=
  originalEHFirstVariation κ Λ hk (originalEHActMetric H.val)
    (original_eh_act_metric_symmetric H.val) (original_eh_act_metric_smooth H.val)
    (fun p _ => original_eh_act_metric_negative H.val H.property p)

/-- Matching only the original action derivatives along compact Lie directions.
The original functional is the derivative on the actual admitted ray H+tK. -/
def MatchesOriginalLieReadings (κ Λ : ℝ) (H : AdmittedOperand Ω)
    (W : MetricSourceProbe Ω →L[ℝ] ℝ) : Prop :=
  ∀ X : CoordinateVectorProbe Ω, W (operandLieTest H X) =
    deriv (fun t : ℝ => originalEHRelativeAction κ Λ wickNativeFlatMetric
      (H.val + t • operandLieTest H X)) 0

theorem occupied_lie_readings_iff_same_current (κ Λ : ℝ) (hk : κ ≠ 0)
    (H : AdmittedOperand Ω) (W : MetricSourceProbe Ω →L[ℝ] ℝ) :
    MatchesOriginalLieReadings κ Λ H W ↔
      constructedSourceDivergence Ω (originalEHActMetric H.val)
        (original_eh_act_metric_smooth H.val) (representedMetricSource W) =
      constructedSourceDivergence Ω (originalEHActMetric H.val)
        (original_eh_act_metric_smooth H.val) (representedMetricSource (operandOriginalReading κ Λ hk H)) := by
  rw [← compact_lie_readings_iff_same_divergence _ _ (original_eh_act_metric_symmetric H.val)]
  unfold MatchesOriginalLieReadings
  simp only [(original_eh_actual_act_hasDerivAt κ Λ hk H.val H.property _).deriv,
    operandOriginalReading, operandLieTest]

private theorem density_current_continuous (g : MetricField) (hg : SmoothCoordinateMetric g)
    (t : Fin 10 → CoordinatePoint → ℝ) (ht : ∀ i, ContDiff ℝ 1 (t i)) (e : Fin 4) :
    Continuous (fun p => classicalTensorDensityCurrent g
      (fun x a b => t (sourceSymmetricIndex a b) x) p e) := by
  change Continuous (fun x => ∑ a : Fin 4, ∑ b : Fin 4, regularDensityCurrentTerm g t a b e x)
  exact continuous_finset_sum _ (fun a _ => continuous_finset_sum _ (fun b _ =>
    regular_density_current_term_continuous g hg t ht a b e))

/-- Compact-test separation applies to the *difference* of the currents.
Equality of Lie readings requires no pointwise divergence assumption for
either rival and does not require agreement on arbitrary symmetric tests. -/
theorem regular_density_currents_of_same_lie_readings (g : MetricField)
    (hg : SmoothCoordinateMetric g) (sym : MetricFieldSymmetric g)
    (V W : MetricSourceProbe Ω →L[ℝ] ℝ)
    (t u : Fin 10 → CoordinatePoint → ℝ) (ht : ∀ i, ContDiff ℝ 1 (t i))
    (hu : ∀ i, ContDiff ℝ 1 (u i))
    (vt : ∀ i φ, representedMetricSource V i φ = ∫ x, t i x * φ x)
    (wu : ∀ i φ, representedMetricSource W i φ = ∫ x, u i x * φ x)
    (agree : ∀ X, V (compactMetricLieCLM Ω g hg X) = W (compactMetricLieCLM Ω g hg X))
    (p : CoordinatePoint) (hp : p ∈ Ω) (e : Fin 4) :
    classicalTensorDensityCurrent g (fun x a b => t (sourceSymmetricIndex a b) x) p e =
      classicalTensorDensityCurrent g (fun x a b => u (sourceSymmetricIndex a b) x) p e := by
  let ct := fun p => classicalTensorDensityCurrent g (fun x a b => t (sourceSymmetricIndex a b) x) p e
  let cu := fun p => classicalTensorDensityCurrent g (fun x a b => u (sourceSymmetricIndex a b) x) p e
  have ht' : Continuous ct := density_current_continuous g hg t ht e
  have hu' : Continuous cu := density_current_continuous g hg u hu e
  have currents := (compact_lie_readings_iff_same_divergence g hg sym V W).mp agree
  apply sub_eq_zero.mp
  apply continuous_scalar_source_tests_separate Ω (fun p => ct p - cu p) (ht'.sub hu') _ p hp
  intro φ
  simp only [sub_mul]
  rw [integral_sub (regular_source_test_product_integrable Ω ct ht' φ)
    (regular_source_test_product_integrable Ω cu hu' φ)]
  apply sub_eq_zero.mpr
  exact (regular_density_current_scalar_pairing Ω g hg _ t ht vt e φ).symm.trans
    ((congrArg (fun L : CoordinateVectorProbe Ω →L[ℝ] ℝ => L (compactVectorTestInsertion Ω e φ))
      currents).trans (regular_density_current_scalar_pairing Ω g hg _ u hu wu e φ))

/-- The same half-pairing normalization as the native metric first variation.
A smooth response may be supplied by its pointwise tensor and independently
declared functional; no action or pre-certified Ward property is required. -/
def RepresentsMetricTensor (g T : MetricField) (W : MetricSourceProbe Ω →L[ℝ] ℝ) : Prop :=
  ∀ i φ, representedMetricSource W i φ =
    ∫ x, sourceDensityCoordinates (raisedSourceTensorDensity g T) i x * φ x

theorem smooth_raised_components (g T : MetricField)
    (hg : SmoothCoordinateMetric g) (hT : SmoothCoordinateMetric T)
    (neg : ∀ p, (g p).det < 0) (i : Fin 10) :
    ContDiff ℝ 1 (sourceDensityCoordinates (raisedSourceTensorDensity g T) i) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  apply ContDiffAt.of_le (n := (∞)) _ (by simp)
  change ContDiffAt ℝ ∞ (fun x => coordinateVolumeDensity g x *
    ∑ k : Fin 4, ∑ l : Fin 4, (g x)⁻¹ (sourceSymmetricPair i).1 k *
      (g x)⁻¹ (sourceSymmetricPair i).2 l * T x k l) p
  exact (eh_volume_density_smooth_at g hg p (neg p)).mul
    (ContDiffAt.sum (fun k _ => ContDiffAt.sum (fun l _ =>
      ((eh_inverse_component_smooth_at g hg p (ne_of_lt (neg p)) _ _).mul
       (eh_inverse_component_smooth_at g hg p (ne_of_lt (neg p)) _ _)).mul
        (hT k l).contDiffAt)))

private theorem eh_response_smooth_on_operand (κ Λ : ℝ) (hk : κ ≠ 0)
    (H : AdmittedOperand Ω) : SmoothCoordinateMetric
      (originalEHGeometricResponse κ Λ (originalEHActMetric H.val)) := by
  let g := originalEHActMetric H.val
  have hg := original_eh_act_metric_smooth H.val
  have neg := original_eh_act_metric_negative H.val H.property
  intro i j
  rw [contDiff_iff_contDiffAt]
  intro p
  have form (x : CoordinatePoint) := congrArg (fun M : Tensor2 => M i j)
    (eh_original_geometric_tensor_identified κ Λ hk g x (neg x))
  have eqf : (fun x => originalEHGeometricResponse κ Λ g x i j) =
      (fun x => -(1/κ) * ((coordinateRicci g x i j -
        (coordinateScalarCurvature g x / 2) * g x i j) + Λ * g x i j)) := funext form
  rw [eqf]
  exact contDiffAt_const.mul (((eh_actual_ricci_smooth_at g hg p (ne_of_lt (neg p)) i j).sub
    ((eh_actual_scalar_curvature_smooth_at g hg p (ne_of_lt (neg p))).div_const 2 |>.mul
      (hg i j).contDiffAt)).add (contDiffAt_const.mul (hg i j).contDiffAt))

/-- On a normal occupied germ, compare both actual currents against the same
compact tests and use the proved off-shell Bianchi identity for the original
geometric response. This establishes closure of a smooth rival on this germ
without assuming its own action or its pointwise divergence. -/
theorem occupied_lie_readings_force_normal_closure (κ Λ : ℝ) (hk : κ ≠ 0)
    (H : AdmittedOperand Ω) (origin : (0 : CoordinatePoint) ∈ Ω)
    (germ : C3NormalizedMetricGerm (originalEHActMetric H.val))
    (T : MetricField) (smooth : SmoothCoordinateMetric T) (sym : MetricFieldSymmetric T)
    (W : MetricSourceProbe Ω →L[ℝ] ℝ)
    (represents : RepresentsMetricTensor (originalEHActMetric H.val) T W)
    (reads : MatchesOriginalLieReadings κ Λ H W) :
    coordinateDivergence (originalEHActMetric H.val) T 0 = 0 := by
  let g := originalEHActMetric H.val
  let U := originalEHGeometricResponse κ Λ g
  let V := operandOriginalReading κ Λ hk H
  have hg := original_eh_act_metric_smooth H.val
  have sg := original_eh_act_metric_symmetric H.val
  have negative := original_eh_act_metric_negative H.val H.property
  have hU : SmoothCoordinateMetric U := eh_response_smooth_on_operand κ Λ hk H
  have sU : MetricFieldSymmetric U := fun p =>
    eh_original_geometric_response_symmetric κ Λ hk g p
      (original_eh_act_metric_lorentz H.val H.property p)
  have originalRep : RepresentsMetricTensor g U V := fun i φ =>
    eh_original_geometric_tensor_represents_action_source κ Λ hk g sg hg _ i φ
  have same (X : CoordinateVectorProbe Ω) : W (operandLieTest H X) = V (operandLieTest H X) :=
    (reads X).trans (original_eh_actual_act_hasDerivAt κ Λ hk H.val H.property _).deriv
  have C := regular_density_currents_of_same_lie_readings g hg sg W V
    _ _ (smooth_raised_components g T hg smooth negative) (smooth_raised_components g U hg hU negative)
    represents originalRep same 0 origin
  rw [source_density_coordinates_recover _ (raised_source_tensor_density_symmetric g T sym),
    source_density_coordinates_recover _ (raised_source_tensor_density_symmetric g U sU)] at C
  have normal := c3_normalized_metric_c2 g germ
  have closeAt := eh_original_geometric_general_closure κ Λ hk g germ
  funext e
  calc
    coordinateDivergence g T 0 e =
        classicalTensorDensityCurrent g (raisedSourceTensorDensity g T) 0 e :=
      (c2_normal_density_current_eq_covariant_divergence g T normal
        (fun i j => (smooth i j).differentiable (by simp) 0) e).symm
    _ = classicalTensorDensityCurrent g (raisedSourceTensorDensity g U) 0 e := C e
    _ = coordinateDivergence g U 0 e := c2_normal_density_current_eq_covariant_divergence g U
        normal (fun i j => (hU i j).differentiable (by simp) 0) e
    _ = 0 := congrFun closeAt e

end AASCOccupiedProfiles
