import OriginalRestrictedEHKernelReceiving
import RegularSourceTestSeparation

/-! Original compact actions determine the complete regular density of a response
at each fixed admitted operand. The ten component observations below are actual
directional derivatives. The factor two and the diagonal/off-diagonal weight
come from varying a symmetric covariant metric. -/

noncomputable section
set_option autoImplicit false
namespace AASCProjectionObservations
open AASCSemanticExhaustion AASCKleinGordon MeasureTheory TopologicalSpace Filter

variable {Ω : Opens CoordinatePoint}

/-- Compactly supported smooth tests separate continuous densities on their open
domain. Density values outside the test domain need satisfy no condition. -/
private theorem eqOn_of_test_integrals {f g : CoordinatePoint → ℝ}
    (hf : ContinuousOn f (Ω : Set CoordinatePoint))
    (hg : ContinuousOn g (Ω : Set CoordinatePoint))
    (same : ∀ φ : ScalarSourceProbe Ω, (∫ p, f p * φ p) = ∫ p, g p * φ p) :
    Set.EqOn f g (Ω : Set CoordinatePoint) := by
  have loc : LocallyIntegrableOn (f - g) (Ω : Set CoordinatePoint) volume :=
    (hf.sub hg).locallyIntegrableOn Ω.isOpen.measurableSet
  have zero : ∀ φ : ScalarSourceProbe Ω, (∫ p, (f p - g p) * φ p) = 0 := by
    intro φ
    simp_rw [sub_mul]
    rw [integral_sub (native_locally_integrable_test_product f
          (hf.locallyIntegrableOn Ω.isOpen.measurableSet) φ)
        (native_locally_integrable_test_product g
          (hg.locallyIntegrableOn Ω.isOpen.measurableSet) φ), same φ, sub_self]
  have hae : ∀ᵐ p, p ∈ (Ω : Set CoordinatePoint) → (f - g) p = 0 :=
    Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero loc (by
      intro ψ smooth compact supp
      let φ : ScalarSourceProbe Ω := ⟨ψ, smooth, compact, supp⟩
      calc
        _ = ∫ p, (f p - g p) * φ p := integral_congr_ae (Eventually.of_forall
          (fun p => mul_comm (ψ p) (f p - g p)))
        _ = 0 := zero φ)
  exact Measure.eqOn_open_of_ae_eq
    ((ae_restrict_iff' Ω.isOpen.measurableSet).mpr (hae.mono (fun p hp h => sub_eq_zero.mp (hp h))))
    Ω.isOpen hf hg

/-- Agreement with the original measured derivatives on single-coordinate
metric probes. All ten components are used, with their physical weights. -/
def MatchesCompactReadings (κ Λ : ℝ) (H : MetricSourceProbe Ω)
    (d : Fin 10 → CoordinatePoint → ℝ) : Prop :=
  ∀ i (φ : ScalarSourceProbe Ω),
    (∫ p, d i p * φ p) = (2 / symmetricSourceWeight i) *
      deriv (fun t : ℝ => originalEHRelativeAction κ Λ wickNativeFlatMetric
        (H + t • sourceTestInsertion i φ)) 0

/-- The measured response fixes the whole density on the interior of the test
domain, without a competitor jet, curvature-order or covariance ansatz. -/
theorem metric_density_of_compact_readings (κ Λ : ℝ) (coupling : κ ≠ 0)
    (H : MetricSourceProbe Ω) (inside : H ∈ wickOriginalMetricNeighborhood Ω)
    (d : Fin 10 → CoordinatePoint → ℝ)
    (continuous : ∀ i, ContinuousOn (d i) (Ω : Set CoordinatePoint))
    (same : MatchesCompactReadings κ Λ H d) :
    ∀ p ∈ Ω, ∀ i, d i p = ehComputedSourceDensity κ Λ (originalEHActMetric H) i p := by
  let g := originalEHActMetric H
  have neg (p : CoordinatePoint) : (g p).det < 0 := original_eh_act_metric_negative H inside p
  intro p hp i
  apply eqOn_of_test_integrals (continuous i) _ _ hp
  · intro x _
    exact (eh_computed_source_density_smooth_at κ Λ g
      (original_eh_act_metric_smooth H) x (neg x) i).continuousAt.continuousWithinAt
  · intro φ
    rw [same i φ, (original_eh_actual_act_hasDerivAt κ Λ coupling H inside _).deriv]
    exact eh_original_euler_response_density κ Λ coupling g
      (original_eh_act_metric_symmetric H) (original_eh_act_metric_smooth H)
      (fun x _ => neg x) i φ

def lowerMetricDensity (g : MetricField) (p : CoordinatePoint) (D : Tensor2) : Tensor2 :=
  (coordinateVolumeDensity g p)⁻¹ • (g p * D * g p)

/-- Lower the uniquely measured contravariant density with the very same
metric and its volume. This recovers the covariant Einstein response. -/
theorem einstein_of_compact_metric_readings (κ Λ : ℝ) (coupling : κ ≠ 0)
    (H : MetricSourceProbe Ω) (inside : H ∈ wickOriginalMetricNeighborhood Ω)
    (d : Fin 10 → CoordinatePoint → ℝ)
    (continuous : ∀ i, ContinuousOn (d i) (Ω : Set CoordinatePoint))
    (same : MatchesCompactReadings κ Λ H d) :
    let g : MetricField := originalEHActMetric H
    ∀ p ∈ Ω, lowerMetricDensity g p (tensorEncode (fun i => d i p)) =
        -(1 / κ) • (coordinateRicci g p -
          (coordinateScalarCurvature g p / 2) • g p + Λ • g p) := by
  intro g p hp
  have h := metric_density_of_compact_readings κ Λ coupling H inside d continuous same p hp
  have encoded : tensorEncode (fun i => d i p) = (2 : ℝ) • ehComputedBulkDensity κ Λ g p := by
    rw [show (fun i => d i p) = fun i => ehComputedSourceDensity κ Λ g i p from funext h]
    change tensorEncodeLinear ((2 : ℝ) • tensorDecode (ehComputedBulkDensity κ Λ g p)) = _
    rw [tensorEncodeLinear.map_smul]
    exact congrArg (fun x : Tensor2 => (2 : ℝ) • x)
      (tensor_encode_decode _ (eh_computed_bulk_density_symmetric κ Λ g
        (original_eh_act_metric_symmetric H) (original_eh_act_metric_smooth H) p))
  rw [encoded]
  exact eh_original_geometric_tensor_identified κ Λ coupling g p
    (original_eh_act_metric_negative H inside p)


/-- Faithfulness of compact measurements fixes an arbitrary continuous covariant
tensor itself. A rival's construction need not use a local curvature expansion. -/
theorem covariant_einstein_of_compact_metric_readings (κ Λ : ℝ) (coupling : κ ≠ 0)
    (H : MetricSourceProbe Ω) (inside : H ∈ wickOriginalMetricNeighborhood Ω)
    (F : MetricField) (continuous : ∀ i j, ContinuousOn (fun x => F x i j) (Ω : Set CoordinatePoint))
    (symmetric : ∀ x ∈ Ω, ∀ i j, F x i j = F x j i)
    (same : MatchesCompactReadings κ Λ H
      (sourceDensityCoordinates (raisedSourceTensorDensity (originalEHActMetric H) F))) :
    let g : MetricField := originalEHActMetric H
    ∀ p ∈ Ω, F p = -(1 / κ) • (coordinateRicci g p -
      (coordinateScalarCurvature g p / 2) • g p + Λ • g p) := by
  intro g p hp
  let data := sourceDensityCoordinates (raisedSourceTensorDensity g F)
  have neg (x : CoordinatePoint) : (g x).det < 0 := original_eh_act_metric_negative H inside x
  have smooth := original_eh_act_metric_smooth H
  have cg : Continuous g :=
    continuous_pi (fun i => continuous_pi (fun j => (smooth i j).continuous))
  have cd (k) : ContinuousOn (data k) (Ω : Set CoordinatePoint) := by
    intro x hx
    have ci := native_clock_inverse_continuousAt g cg.continuousAt (ne_of_lt (neg x))
    have entry (i j : Fin 4) : ContinuousWithinAt (fun y => (g y)⁻¹ i j)
        (Ω : Set CoordinatePoint) x :=
      ((continuousAt_pi.mp (continuousAt_pi.mp ci i)) j).continuousWithinAt
    apply (eh_volume_density_smooth_at g smooth x (neg x)).continuousAt.continuousWithinAt.mul
    apply tendsto_finset_sum
    intro i _
    apply tendsto_finset_sum
    intro j _
    exact ((entry _ i).mul (entry _ j)).mul (continuous i j x hx)
  have identified := einstein_of_compact_metric_readings κ Λ coupling H inside data cd same p hp
  have coords : (fun i => data i p) = tensorDecode (raisedSourceTensorDensity g F p) := by
    funext i
    fin_cases i <;> rfl
  have rsym : ∀ i j, raisedSourceTensorDensity g F p i j = raisedSourceTensorDensity g F p j i :=
    raised_source_tensor_density_symmetric g (fun _ => F p) (fun _ => symmetric p hp) p
  rw [coords, tensor_encode_decode _ rsym] at identified
  have unit : IsUnit (g p).det := isUnit_iff_ne_zero.mpr (ne_of_lt (neg p))
  have vne : coordinateVolumeDensity g p ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (neg_pos.mpr (neg p)))
  have symG : (g p).transpose = g p := by
    ext i j
    exact original_eh_act_metric_symmetric H p j i
  have symB : (g p)⁻¹.transpose = (g p)⁻¹ := by rw [Matrix.transpose_nonsing_inv, symG]
  have raised : raisedSourceTensorDensity g F p =
      coordinateVolumeDensity g p • ((g p)⁻¹ * F p * (g p)⁻¹) := by
    ext i j
    simp only [raisedSourceTensorDensity, Matrix.smul_apply, smul_eq_mul,
      native_raise_source_matrix_identity _ _ symB]
  have cancel (Q : Tensor2) : g p * ((g p)⁻¹ * Q * (g p)⁻¹) * g p = Q := by
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ unit, Matrix.one_mul,
      Matrix.nonsing_inv_mul_cancel_right _ _ unit]
  change lowerMetricDensity g p (raisedSourceTensorDensity g F p) = _ at identified
  simpa only [lowerMetricDensity, raised, Matrix.mul_smul, Matrix.smul_mul,
    cancel, smul_smul, inv_mul_cancel₀ vne, one_smul] using identified

#print axioms covariant_einstein_of_compact_metric_readings
#print axioms metric_density_of_compact_readings
#print axioms einstein_of_compact_metric_readings
end AASCProjectionObservations
