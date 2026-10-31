import EHGeometryTransport

/-! Construct an actual inhabitant of the regular first-response class.
The operator is computed from the actual inverse metric and Levi-Civita
curvature. Naturality, locality, symmetry, first-response and Bianchi closure
are proved, not fields. No claim about a particular native Cauchy development
or original physical protocol interpretation is made by this geometry alone. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def actualEinsteinResponse : MetricFieldResponse :=
  fun g p => coordinateRicci g p-(1/2:ℝ) • coordinateScalarMetric g p

theorem actual_einstein_response_natural : RegularLorentzResponseNatural actualEinsteinResponse := by
  intro F p B regularF derivative g domain
  obtain ⟨L,frame⟩ := domain.2.2
  have nd := lorentz_frame_metric_nondegenerate g (F p) L frame
  have regular3 : ContDiffAt ℝ 3 F p := regularF.of_le (by simp)
  have ricci := coordinate_ricci_regular_natural g domain.1 F p domain.2.1 nd regular3 B derivative
  have scalar := coordinate_scalar_regular_natural g domain.1 F p domain.2.1 nd regular3 B derivative
  simp only [actualEinsteinResponse,coordinateScalarMetric,ricci,scalar,
    Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,coordinateMetricPullback_matrix]

theorem actual_einstein_response_twojet_local : RegularLorentzTwoJetLocal actualEinsteinResponse := by
  intro g h p dg dh equal
  obtain ⟨B,frame⟩ := dg.2.2
  obtain ⟨C,hframe⟩ := dh.2.2
  have curv := c2_general_curvature_twojet_congr g h p dg.1 dh.1 dg.2.1 dh.2.1
    (lorentz_frame_metric_nondegenerate g p B frame)
    (lorentz_frame_metric_nondegenerate h p C hframe) equal
  have ricci : coordinateRicci g p=coordinateRicci h p := by
    unfold coordinateRicci
    rw [equal.1,curv]
  simp only [actualEinsteinResponse,coordinateScalarMetric,coordinateScalarCurvature,
    equal.1,ricci]

theorem actual_einstein_response_symmetric (g : MetricField) (p : CoordinatePoint)
    (domain : C2LorentzMetricAt g p) (a b : Fin 4) :
    actualEinsteinResponse g p a b=actualEinsteinResponse g p b a := by
  change coordinateRicci g p a b-(1/2:ℝ)*(coordinateScalarCurvature g p*g p a b)=_
  rw [coordinate_ricci_symmetric_on_regular_lorentz g p domain a b,domain.1 p a b]
  rfl

theorem normalized_actual_ricci_is_original_curvature_contraction (g : MetricField)
    (germ : NormalizedSmoothMetricGerm g) :
    coordinateRicci g 0=ricciResponse (originalNormalizedCurvature g germ) := by
  rw [ricciResponse_eq_tensorRicci]
  change tensorRicci (g 0)⁻¹ (loweredConnectionCurvature g (leviCivitaCoefficients g) 0)=
    tensorRicci metric (loweredConnectionCurvature g (leviCivitaCoefficients g) 0)
  rw [germ.2.2.1,canonical_metric_inverse]

theorem normalized_actual_scalar_is_original_curvature_contraction (g : MetricField)
    (germ : NormalizedSmoothMetricGerm g) :
    coordinateScalarMetric g 0=scalarMetricResponse (originalNormalizedCurvature g germ) := by
  change coordinateScalarCurvature g 0 • g 0=
    scalarCurvatureResponse (originalNormalizedCurvature g germ) • metric
  rw [germ.2.2.1]
  congr 1
  rw [scalarCurvatureResponse_eq_contraction,
    ← normalized_actual_ricci_is_original_curvature_contraction g germ]
  change matrixContractionLinear (g 0)⁻¹ (coordinateRicci g 0)=
    matrixContractionLinear metric (coordinateRicci g 0)
  rw [germ.2.2.1,canonical_metric_inverse]

theorem normalized_actual_einstein_is_original_curvature_response (g : MetricField)
    (germ : NormalizedSmoothMetricGerm g) :
    actualEinsteinResponse g 0=ricciResponse (originalNormalizedCurvature g germ)-
      (1/2:ℝ) • scalarMetricResponse (originalNormalizedCurvature g germ) := by
  rw [actualEinsteinResponse,normalized_actual_ricci_is_original_curvature_contraction g germ,
    normalized_actual_scalar_is_original_curvature_contraction g germ]

theorem actual_einstein_flat_baseline_zero : actualEinsteinResponse flatMetricField 0=0 := by
  have germ : NormalizedSmoothMetricGerm flatMetricField := by
    rw [← hessianMetricPolynomial_flat]
    exact hessianMetricPolynomial_normalized 0
  have curv : originalNormalizedCurvature flatMetricField germ=0 := by
    change c2NormalizedLeviCivitaCurvature flatMetricField _=0
    rw [c2_normalizedLeviCivitaCurvature_eq_jet]
    unfold c2NormalizedMetricJetCurvature
    have hessian : c2MetricHessian flatMetricField 0 germ.1
        (original_smooth_normalized_is_c2 flatMetricField germ).2.1=0 := by
      apply Subtype.ext
      funext a b c d
      simp [c2MetricHessian,flatMetricField,scalarSecondPartial,scalarPartial]
    rw [hessian,map_zero]
  rw [normalized_actual_einstein_is_original_curvature_response flatMetricField germ,curv]
  simp

theorem actual_einstein_original_curvature_first_response : OriginalCurvatureFirstResponse actualEinsteinResponse := by
  constructor
  · intro g h k hg hh hk sum
    rw [normalized_actual_einstein_is_original_curvature_response k hk,
      normalized_actual_einstein_is_original_curvature_response g hg,
      normalized_actual_einstein_is_original_curvature_response h hh,sum,
      actual_einstein_flat_baseline_zero,map_add,map_add]
    module
  · intro r g k hg hk scale
    rw [normalized_actual_einstein_is_original_curvature_response k hk,
      normalized_actual_einstein_is_original_curvature_response g hg,scale,
      actual_einstein_flat_baseline_zero,map_smul,map_smul]
    module

theorem actual_einstein_regular_core : RegularLorentzResponseCore actualEinsteinResponse :=
  original_curvature_response_derives_regular_core actualEinsteinResponse
    actual_einstein_response_natural actual_einstein_response_twojet_local
    actual_einstein_original_curvature_first_response actual_einstein_response_symmetric

theorem actual_einstein_general_bianchi_closure : GeneralNormalMetricResponseClosure actualEinsteinResponse := by
  intro g germ
  change coordinateDivergenceLinear g
    (ricciTensorGerm g germ-(1/2:ℝ) • scalarMetricTensorGerm g germ)=0
  rw [map_sub,map_smul,c3_normal_divergence_ricci_germ,c3_normal_divergence_scalar_metric_germ]
  module

theorem actual_einstein_full_envelope_active : FullLorentzEnvelopeResponseActive actualEinsteinResponse := by
  rintro ⟨c,pure⟩
  obtain ⟨coeff,normal,unique⟩ := regular_lorentz_coordinate_response_normal_form
    actualEinsteinResponse actual_einstein_regular_core
  have einstein : ∀ (g : MetricField) (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint),
      MetricFieldSymmetric g → (∀ i j,ContDiffAt ℝ 2 (fun x => g x i j) p) →
        LorentzFrameAt g p B → actualEinsteinResponse g p=
          (1:ℝ) • coordinateRicci g p+(-(1:ℝ)/2) • coordinateScalarMetric g p+(0:ℝ) • g p := by
    intro g p B hs hr hf
    simp only [actualEinsteinResponse,one_smul,zero_smul,add_zero]
    module
  have baseline : ∀ (g : MetricField) (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint),
      MetricFieldSymmetric g → (∀ i j,ContDiffAt ℝ 2 (fun x => g x i j) p) →
        LorentzFrameAt g p B → actualEinsteinResponse g p=
          (0:ℝ) • coordinateRicci g p+(0:ℝ) • coordinateScalarMetric g p+c • g p := by
    intro g p B hs hr hf
    simpa only [zero_smul,zero_add] using pure g p B hs hr hf
  have impossible := (unique ((1,-(1:ℝ)/2,0) : ℝ × ℝ × ℝ) einstein).trans
    (unique ((0,0,c) : ℝ × ℝ × ℝ) baseline).symm
  have one_zero : (1:ℝ)=0 := congrArg Prod.fst impossible
  norm_num at one_zero

theorem actual_einstein_constructs_active_regular_first_response :
    RegularLorentzResponseCore actualEinsteinResponse ∧
      GeneralNormalMetricResponseClosure actualEinsteinResponse ∧
      FullLorentzEnvelopeResponseActive actualEinsteinResponse ∧
      ∃! ac : ℝ × ℝ,ac.1≠0 ∧ CoordinateEinsteinResponseForm actualEinsteinResponse ac.1 ac.2 :=
  ⟨actual_einstein_regular_core,actual_einstein_general_bianchi_closure,
    actual_einstein_full_envelope_active,regular_general_envelope_unique_einstein_response
      actualEinsteinResponse actual_einstein_regular_core actual_einstein_general_bianchi_closure
        actual_einstein_full_envelope_active⟩

end
end AASCSemanticExhaustion
