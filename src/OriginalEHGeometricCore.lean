import OriginalEHGeometricNaturality
import ActualEinsteinRegularResponse

namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Filter
open scoped Topology

theorem eh_original_geometric_tensor_as_actual (κ Λ : ℝ) (hk : κ ≠ 0)
    (g : MetricField) (p : CoordinatePoint) (negative : (g p).det < 0) :
    originalEHGeometricResponse κ Λ g p =
      -(1/κ) • actualEinsteinResponse g p + (-(1/κ) * Λ) • g p := by
  rw [eh_original_geometric_tensor_identified κ Λ hk g p negative]
  ext i j
  simp only [actualEinsteinResponse,coordinateScalarMetric,
    Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

theorem eh_normalized_metric_determinant_negative (g : MetricField)
    (germ : C2NormalizedMetricGerm g) : (g 0).det < 0 := by
  rw [germ.2.2.1,canonical_lorentz_metric_det]
  norm_num

theorem eh_original_geometric_curvature_first_response (κ Λ : ℝ) (hk : κ ≠ 0) :
    OriginalCurvatureFirstResponse (originalEHGeometricResponse κ Λ) := by
  have normal (g : MetricField) (hg : NormalizedSmoothMetricGerm g) :
      originalEHGeometricResponse κ Λ g 0 =
        -(1/κ) • actualEinsteinResponse g 0 + (-(1/κ)*Λ) • metric := by
    rw [eh_original_geometric_tensor_as_actual κ Λ hk g 0
      (eh_normalized_metric_determinant_negative g (original_smooth_normalized_is_c2 g hg)),hg.2.2.1]
  have flatGerm : NormalizedSmoothMetricGerm flatMetricField := by
    rw [← hessianMetricPolynomial_flat]
    exact hessianMetricPolynomial_normalized 0
  have flat : originalEHGeometricResponse κ Λ flatMetricField 0 = (-(1/κ)*Λ) • metric := by
    rw [normal flatMetricField flatGerm,actual_einstein_flat_baseline_zero,smul_zero,zero_add]
  constructor
  · intro g h k hg hh hkg curvature
    rw [normal k hkg,normal g hg,normal h hh,flat,
      actual_einstein_original_curvature_first_response.1 g h k hg hh hkg curvature,
      actual_einstein_flat_baseline_zero]
    module
  · intro r g k hg hkg curvature
    rw [normal k hkg,normal g hg,flat,
      actual_einstein_original_curvature_first_response.2 r g k hg hkg curvature,
      actual_einstein_flat_baseline_zero]
    module

theorem eh_original_geometric_response_regular_core (κ Λ : ℝ) (hk : κ ≠ 0) :
    RegularLorentzResponseCore (originalEHGeometricResponse κ Λ) :=
  original_curvature_response_derives_regular_core _
    (eh_original_geometric_response_regular_natural κ Λ hk)
    (eh_original_geometric_response_twojet_local κ Λ hk)
    (eh_original_geometric_curvature_first_response κ Λ hk)
    (eh_original_geometric_response_symmetric κ Λ hk)

theorem eh_original_geometric_general_closure (κ Λ : ℝ) (hk : κ ≠ 0) :
    GeneralNormalMetricResponseClosure (originalEHGeometricResponse κ Λ) := by
  intro g germ
  have cg : ContinuousAt g 0 := continuousAt_pi.mpr (fun a => continuousAt_pi.mpr
    (fun b => (germ.2.1 a b).continuousAt))
  have near : ∀ᶠ p in 𝓝 0, (g p).det < 0 :=
    (((continuous_id : Continuous (fun M : Tensor2 => M)).matrix_det).continuousAt.comp cg).eventually
      (eventually_lt_nhds (eh_normalized_metric_determinant_negative g (c3_normalized_metric_c2 g germ)))
  have equal : originalEHGeometricResponse κ Λ g =ᶠ[𝓝 0]
      -(1/κ) • actualEinsteinResponse g + (-(1/κ)*Λ) • g := by
    filter_upwards [near] with p hp
    exact eh_original_geometric_tensor_as_actual κ Λ hk g p hp
  rw [coordinate_divergence_germ_congruence g _ _ equal]
  change coordinateDivergenceLinear g
    (-(1/κ) • (ricciTensorGerm g germ - (1/2:ℝ) • scalarMetricTensorGerm g germ) +
      (-(1/κ)*Λ) • metricTensorGerm g germ) = 0
  rw [map_add,map_smul,map_sub,map_smul,map_smul,c3_normal_divergence_ricci_germ,
    c3_normal_divergence_scalar_metric_germ,c3_normal_divergence_metric_germ]
  module

theorem eh_original_geometric_full_envelope_active (κ Λ : ℝ) (hk : κ ≠ 0) :
    FullLorentzEnvelopeResponseActive (originalEHGeometricResponse κ Λ) := by
  rintro ⟨c,pure⟩
  apply actual_einstein_full_envelope_active
  refine ⟨-κ*c-Λ,?_⟩
  intro g p B sg hg frame
  have h := pure g p B sg hg frame
  rw [eh_original_geometric_tensor_as_actual κ Λ hk g p
    (native_lorentz_frame_determinant_negative g p B frame)] at h
  ext i j
  have component := congrArg (fun M : Tensor2 => M i j) h
  change -(1/κ) * actualEinsteinResponse g p i j + (-(1/κ)*Λ) * g p i j = c * g p i j at component
  change actualEinsteinResponse g p i j = (-κ*c-Λ) * g p i j
  field_simp [hk] at component
  nlinarith

theorem eh_original_geometric_response_unique_coefficients (κ Λ : ℝ) (hk : κ ≠ 0) :
    ∃! ac : ℝ × ℝ, ac.1 ≠ 0 ∧ CoordinateEinsteinResponseForm (originalEHGeometricResponse κ Λ) ac.1 ac.2 :=
  regular_general_envelope_unique_einstein_response _
    (eh_original_geometric_response_regular_core κ Λ hk)
    (eh_original_geometric_general_closure κ Λ hk)
    (eh_original_geometric_full_envelope_active κ Λ hk)

theorem eh_original_geometric_coefficients_exact (κ Λ : ℝ) (hk : κ ≠ 0) :
    CoordinateEinsteinResponseForm (originalEHGeometricResponse κ Λ)
      (-(1/κ)) (-(1/κ)*Λ) := by
  intro g p B sg hg frame
  exact eh_original_geometric_tensor_as_actual κ Λ hk g p
    (native_lorentz_frame_determinant_negative g p B frame)

end
end AASCSemanticExhaustion
