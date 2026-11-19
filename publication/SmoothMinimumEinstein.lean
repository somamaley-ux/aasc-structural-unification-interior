import MinimumMetricResponseOrder

/-! Smooth-only classification at the least differential order. The external
geometric implication in the published Lovelock theorem is identified by
`NormalResponseSecondSymmetries`. The differential regularity of the response
profile is explicit. Once the dimension bound enforces affinity, the physical
coefficient test requires ordinary divergence only on one concrete smooth
cubic metric, so no transfer to nonsmooth metrics is assumed. -/
namespace AASCSemanticExhaustion
noncomputable section
open Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

private theorem normalized_operand {g : MetricField} (germ : NormalizedSmoothMetricGerm g) :
    SmoothLorentzOperand g 0 :=
  ⟨germ.1, fun a b => (germ.2.1 a b).of_le le_top, ContinuousLinearEquiv.refl ℝ CoordinatePoint,
    c2_normalizedMetric_identity_frame g (original_smooth_normalized_is_c2 g germ)⟩

private theorem smooth_two_jet_value {E : MetricFieldResponse}
    (hl : SmoothMetricResponseOrderAtMost E 2) {g h p}
    (hg : SmoothLorentzOperand g p) (hh : SmoothLorentzOperand h p)
    (jet : MetricTwoJetEqualAt g h p) : E g p = E h p :=
  hl g h p hg hh ⟨jet, by intro k lo hi; change k ≤ 2 at hi; omega⟩

private theorem smooth_hessian_gauge (E : MetricFieldResponse)
    (hn : SmoothMetricResponseNatural E) (hl : SmoothMetricResponseOrderAtMost E 2) :
    HessianGaugeInvariant (metricHessianResponseAt E 0) := by
  intro H K hK
  obtain ⟨T, laws, gauge⟩ := hK
  have heq := smooth_two_jet_value hl
    (normalized_operand (local_cubic_metric_pullback_germ _ (hessianMetricPolynomial_normalized H)
      (raisedCubicCoordinate T) (raisedCubicCoordinate_laws T laws)))
    (normalized_operand (hessianMetricPolynomial_normalized (H+K))) (cubic_gauge_actual_twojet H K T laws gauge)
  have hc := hn (cubicCoordinateMap (raisedCubicCoordinate T)) 0 (ContinuousLinearEquiv.refl ℝ CoordinatePoint)
    ((cubicCoordinateMap_smooth _).contDiffAt.of_le le_top) (cubicCoordinateMap_hasFDerivAt_zero _) _
    (by simpa only [cubicCoordinateMap_zero] using normalized_operand (hessianMetricPolynomial_normalized H))
  rw [cubic_coordinate_jacobian_zero _ (raisedCubicCoordinate_laws T laws), cubicCoordinateMap_zero] at hc
  simp only [Matrix.transpose_one, one_mul, mul_one] at hc
  rw [metricHessianResponseAt_origin, metricHessianResponseAt_origin]
  exact heq.symm.trans hc

private theorem smooth_hessian_covariant (E : MetricFieldResponse)
    (hn : SmoothMetricResponseNatural E) (hl : SmoothMetricResponseOrderAtMost E 2) :
    HessianCovariant (metricHessianResponseAt E 0) := by
  intro L H K transport
  have heq := smooth_two_jet_value hl
    (normalized_operand (normalized_lorentz_pullback_germ _ (hessianMetricPolynomial_normalized H) L))
    (normalized_operand (hessianMetricPolynomial_normalized K)) (lorentz_frame_actual_twojet L H K transport)
  have hc := hn (lorentzCoordinateMap L) 0 (lorentzCoordinateEquiv L)
    ((lorentzCoordinateMap_smooth L).contDiffAt.of_le le_top) (lorentzCoordinateMap_hasFDerivAt L 0) _
    (by simpa only [lorentzCoordinateMap_zero] using normalized_operand (hessianMetricPolynomial_normalized H))
  rw [lorentzCoordinateMap_jacobian, lorentzCoordinateMap_zero] at hc
  rw [metricHessianResponseAt_origin, metricHessianResponseAt_origin]
  exact heq.symm.trans hc

private theorem smooth_hessian_affine_of_div2 (E : MetricFieldResponse)
    (regular : ContDiff ℝ 2 (metricHessianResponseAt E 0)) (symmetries : NormalResponseSecondSymmetries E) :
    HessianAffine (metricHessianResponseAt E 0) := by
  let F := metricHessianResponseAt E 0
  have form := eq_baseline_add_linear_of_zero_second_derivative F (regular.differentiable (by norm_num))
    ((regular.fderiv_right (m := 1) (by norm_num)).differentiable (by simp))
    (response_hessian_zero_of_four_dimensional_symmetries E symmetries)
  constructor
  · intro H K
    change F (H+K) = F H + F K - F 0
    rw [form (H+K), form H, form K, map_add]
    abel
  · intro r H
    change F (r • H) = r • (F H - F 0) + F 0
    rw [form (r • H), form H, map_smul, add_sub_cancel_left]
    exact add_comm _ _

private def SmoothResponseTriplet (E : MetricFieldResponse) (c : ℝ × ℝ × ℝ) : Prop :=
  ∀ g p, SmoothLorentzOperand g p →
    E g p = c.1 • coordinateRicci g p + c.2.1 • coordinateScalarMetric g p + c.2.2 • g p

private theorem smooth_response_triplet (E : MetricFieldResponse) (hn : SmoothMetricResponseNatural E)
    (hl : SmoothMetricResponseOrderAtMost E 2) (regular : ContDiff ℝ 2 (metricHessianResponseAt E 0))
    (symmetries : NormalResponseSecondSymmetries E)
    (symmetric : ∀ g p, SmoothLorentzOperand g p → ∀ i j, E g p i j = E g p j i) :
    ∃! c, SmoothResponseTriplet E c := by
  have hs : HessianSymmetric (metricHessianResponseAt E 0) := by
    intro H a b
    rw [metricHessianResponseAt_origin]
    exact symmetric _ 0 (normalized_operand (hessianMetricPolynomial_normalized H)) a b
  obtain ⟨c, poly, unique⟩ := hessian_response_unique_normal_form _ (smooth_hessian_affine_of_div2 E regular symmetries)
    hs (smooth_hessian_covariant E hn hl) (smooth_hessian_gauge E hn hl)
  simp only [metricHessianResponseAt_origin] at poly unique
  refine ⟨c, ?_, ?_⟩
  · intro g p hg
    obtain ⟨B, frame⟩ := hg.2.2
    obtain ⟨normalized,germ⟩ := smooth_normal_frame_operand g p B hg frame
    let H := c2MetricHessian _ 0 germ.1 germ.2.1
    have equal := smooth_two_jet_value hl normalized
      (normalized_operand (hessianMetricPolynomial_normalized H)) (c2_normalized_metric_matches_receiver _ germ)
    have transformed := hn (pointNormalChartMap g p B) 0 B ((pointNormalChartMap_analytic g p B).contDiffAt.of_le le_top)
      (pointNormalChartMap_hasFDerivAt g p B hg.1) g (by simpa only [pointNormalChartMap_zero] using hg)
    simp only [pointNormalChartMap_pullback, pointNormalChartMap_zero,
      pointNormalChartMap_jacobian g p B hg.1] at transformed
    apply (actual_coordinate_response_identity_iff g p B hg.1
      (fun a b => (hg.2.1 a b).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
      frame _ _ _ _).mp
    rw [← transformed, equal, poly, framedActualConnectionCurvature_eq_normal_chart]
    simp only [c2_normalChartCurvature, c2_normalizedLeviCivitaCurvature_eq_jet]
    rfl
  · intro other hother
    apply unique other
    intro H
    let g := hessianMetricPolynomial H
    have h := hessianMetricPolynomial_c2_normalized H
    let B := ContinuousLinearEquiv.refl ℝ CoordinatePoint
    have frame := c2_normalizedMetric_identity_frame _ h
    have record := hother g 0 (normalized_operand (hessianMetricPolynomial_normalized H))
    have co := (actual_coordinate_response_identity_iff g 0 B h.1 h.2.1 frame _ _ _ _).mpr record
    simpa only [B, g, h, frame, coordinateFrameMatrix_refl, Matrix.transpose_one, one_mul, mul_one,
      framedActualConnectionCurvature_eq_normal_chart, c2_normalChartCurvature_retraction,
      c2_normalizedLeviCivitaCurvature_eq_jet, c2NormalizedMetricJetCurvature_receiver] using co

/-- Original smooth metric fields and smooth Lorentzian germs, on their full
domain, with equality of the output tensor in its original coordinates. -/
def SmoothEinsteinResponseForm (E : MetricFieldResponse) (a b : ℝ) : Prop :=
  ∀ g p, SmoothLorentzOperand g p → E g p = a • actualEinsteinResponse g p + b • g p

/-- Classification at the minimum order, conditional on the Lovelock
differentiated coefficient symmetries. Only the divergence test on the
actual smooth cubic metric with nonzero scalar-curvature gradient is needed
to determine the relative Ricci and scalar-trace coefficients. -/
theorem smooth_minimal_einstein_form_of_cubic_ward (E : MetricFieldResponse)
    (hn : SmoothMetricResponseNatural E) (hl : SmoothMetricResponseOrderAtMost E 2)
    (regular : ContDiff ℝ 2 (metricHessianResponseAt E 0)) (symmetries : NormalResponseSecondSymmetries E)
    (symmetric : ∀ g p, SmoothLorentzOperand g p → ∀ i j, E g p i j = E g p j i)
    (active : SmoothMetricResponseActive E)
    (closed : coordinateDivergence (cubicMetricField scalarGradientWitnessJet)
      (E (cubicMetricField scalarGradientWitnessJet)) 0 = 0) :
    ∃! ac : ℝ × ℝ, ac.1 ≠ 0 ∧ SmoothEinsteinResponseForm E ac.1 ac.2 := by
  obtain ⟨⟨a,b,c⟩, form, unique⟩ := smooth_response_triplet E hn hl regular symmetries symmetric
  let g := cubicMetricField scalarGradientWitnessJet
  have germ : C3NormalizedMetricGerm g := cubicMetricField_c3_normalized _ scalarGradientWitnessJet_metric_symmetry
  have near : E g =ᶠ[𝓝 0] a • coordinateRicci g + b • coordinateScalarMetric g + c • g := by
    filter_upwards [cubic_witness_lorentz_frames_near_zero] with p hp
    exact form g p ⟨germ.1, fun i j =>
      (contDiff_const.add (cubicPolynomial_smooth (scalarGradientWitnessJet i j))).contDiffAt.of_le le_top, hp⟩
  have ds : coordinateDivergence g (a • coordinateRicci g + b • coordinateScalarMetric g + c • g) 0 = 0 := by
    rw [← coordinate_divergence_germ_congruence g _ _ near]
    exact closed
  have lock := (c3_normal_geometric_coefficient_lock_iff g germ actual_scalar_gradient_witness_nonzero a b c).mp ds
  have einstein : SmoothEinsteinResponseForm E a c := by
    intro h p hh
    rw [form h p hh]
    exact MetricProjectionAudit.einstein_combination _ _ _ a b c lock
  have nonzero : a ≠ 0 := by
    intro h
    apply active
    refine ⟨c, fun f p hf => ?_⟩
    rw [einstein f p hf, h, zero_smul, zero_add]
  refine ⟨(a,c), ⟨nonzero, einstein⟩, ?_⟩
  rintro ⟨a',c'⟩ ⟨_, other⟩
  have other' : SmoothResponseTriplet E (a',-a'/2,c') := by
    intro f p hf
    rw [other f p hf]
    exact (MetricProjectionAudit.einstein_combination _ _ _ a' (-a'/2) c' rfl).symm
  have same := unique _ other'
  have first : a' = a := congrArg Prod.fst same
  have last : c' = c := congrArg (fun x : ℝ × ℝ × ℝ => x.2.2) same
  exact Prod.ext first last

/-- Every active coefficient pair is attained at the minimum, including an
arbitrary metric baseline. The witness is an actual member of the already
constructed action family, parameterized to realize the requested pair. -/
theorem every_active_einstein_pair_occurs_at_minimum (a b : ℝ) (ha : a ≠ 0) :
    ∃ E : MetricFieldResponse, SmoothMetricResponseNatural E ∧
      GeneralNormalMetricResponseClosure E ∧ SmoothMetricResponseActive E ∧
      (∀ g p, SmoothLorentzOperand g p → ∀ i j, E g p i j = E g p j i) ∧
      IsLeast {n : ℕ | SmoothMetricResponseOrderAtMost E n} 2 ∧
      SmoothEinsteinResponseForm E a b := by
  let κ := -(1/a)
  let Λ := b/a
  have hk : κ ≠ 0 := by dsimp [κ]; exact neg_ne_zero.mpr (one_div_ne_zero ha)
  let E := originalEHGeometricResponse κ Λ
  have hn := eh_original_geometric_response_regular_natural κ Λ hk
  have hl := eh_original_geometric_response_twojet_local κ Λ hk
  have active := smooth_activity_of_regular_two_jet_activity E hn hl (eh_original_geometric_full_envelope_active κ Λ hk)
  refine ⟨E, original_eh_natural_under_smooth_coordinates κ Λ hk, eh_original_geometric_general_closure κ Λ hk, active, ?_,
    occupied_eh_least_intrinsic_order κ Λ hk, ?_⟩
  · intro g p hg
    exact eh_original_geometric_response_symmetric κ Λ hk g p
      ⟨hg.1, fun i j => (hg.2.1 i j).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)), hg.2.2⟩
  · intro g p hg
    obtain ⟨B, frame⟩ := hg.2.2
    have eq := eh_original_geometric_coefficients_exact κ Λ hk g p B hg.1
      (fun i j => (hg.2.1 i j).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) frame
    have ca : -(1/κ) = a := by dsimp [κ]; field_simp
    have cb : -(1/κ)*Λ = b := by rw [ca]; dsimp [Λ]; field_simp
    rw [cb, ca] at eq
    exact eq

end
end AASCSemanticExhaustion
