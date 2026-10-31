import C2MetricLeviCivita

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

theorem c2_coordinateMetricPullback_contDiffAt (g : MetricField) (F : CoordinatePoint → CoordinatePoint)
    (p : CoordinatePoint) (chart : ContDiffAt ℝ ⊤ F p)
    (regular : ∀ i j, ContDiffAt ℝ 2 (fun x => g x i j) (F p)) (a b : Fin 4) :
    ContDiffAt ℝ 2 (fun x => coordinateMetricPullback g F x a b) p := by
  unfold coordinateMetricPullback
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (((coordinateJacobian_contDiffAt F p chart i a).of_le (by simp)).mul
    ((regular i j).comp p (chart.of_le (by simp)))).mul
      ((coordinateJacobian_contDiffAt F p chart j b).of_le (by simp))

theorem c2_quadratic_identity_metric_pullback_partial (g : MetricField)
    (smooth : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) 0)
    (Q : CoordinateQuadraticArray) (symmetric : ∀ i a b, Q i a b = Q i b a)
    (a b c : Fin 4) :
    scalarPartial (fun x => coordinateMetricPullback g (quadraticIdentityMap Q) x a b) 0 c =
      metricPartial g 0 a b c + (∑ i : Fin 4, g 0 i b * Q i a c) + (∑ j : Fin 4, g 0 a j * Q j b c) := by
  let F := quadraticIdentityMap Q
  have hF : HasFDerivAt F (ContinuousLinearMap.id ℝ CoordinatePoint) 0 :=
    quadraticCoordinateMap_hasFDerivAt_zero _ _ _
  have hfzero : F 0 = 0 := quadraticIdentityMap_zero Q
  have hjzero : coordinateJacobian F 0 = 1 := quadraticIdentityMap_jacobian_zero Q symmetric
  have hj (i k : Fin 4) : HasFDerivAt (fun x => coordinateJacobian F x i k)
      (quadraticJacobianDerivative Q i k) 0 :=
    quadraticJacobian_hasFDerivAt _ _ _ symmetric 0 i k
  have hb (i j : Fin 4) : HasFDerivAt (fun x => g (F x) i j)
      (fderiv ℝ (fun x => g x i j) 0) 0 := by
    have hdg : DifferentiableAt ℝ (fun x => g x i j) (F 0) := by
      simpa only [hfzero] using (smooth i j).differentiableAt (by simp)
    have hd := hdg.hasFDerivAt.comp 0 hF
    change HasFDerivAt (fun x => g (F x) i j)
      ((fderiv ℝ (fun x => g x i j) (F 0)).comp (ContinuousLinearMap.id ℝ CoordinatePoint)) 0 at hd
    simpa only [hfzero, ContinuousLinearMap.comp_id] using hd
  have ht (i j : Fin 4) := ((hj i a).mul (hb i j)).mul (hj j b)
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => ht i j))
  simp only [Pi.mul_apply, hfzero, hjzero] at hs
  have hd := hs.fderiv
  change fderiv ℝ (fun x => coordinateMetricPullback g F x a b) 0 = _ at hd
  unfold scalarPartial
  change fderiv ℝ (fun x => coordinateMetricPullback g F x a b) 0 (Pi.single c 1) = _
  rw [hd]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, smul_eq_mul, quadraticJacobianDerivative_basis]
  change (∑ i : Fin 4, ∑ j : Fin 4,
    (((1 : Tensor2) i a * g 0 i j) * Q j b c + (1 : Tensor2) j b *
      ((1 : Tensor2) i a * metricPartial g 0 i j c + g 0 i j * Q i a c))) = _
  simp [Matrix.one_apply, Finset.sum_add_distrib, mul_add, ite_mul, mul_ite]
  ring

theorem c2_normalizing_metric_partial_zero (g : MetricField) (symmetric : MetricFieldSymmetric g)
    (smooth : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) 0) (value : g 0 = metric)
    (a b c : Fin 4) :
    scalarPartial (fun x => coordinateMetricPullback g (normalizingCoordinateMap g) x a b) 0 c = 0 := by
  have hn : (g 0).det ≠ 0 := by rw [value, canonical_lorentz_metric_det]; norm_num
  have hc := leviCivita_metric_compatible g symmetric 0 hn a b c
  have h1 : (∑ i : Fin 4, g 0 i b * normalCoordinateCorrection g i a c) =
      -(∑ i : Fin 4, leviCivitaCoefficients g 0 i c a * g 0 i b) := by
    simp only [normalCoordinateCorrection, mul_neg, Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [leviCivita_torsion_free g symmetric 0 i a c]
    ring
  have h2 : (∑ i : Fin 4, g 0 a i * normalCoordinateCorrection g i b c) =
      -(∑ i : Fin 4, leviCivitaCoefficients g 0 i c b * g 0 a i) := by
    simp only [normalCoordinateCorrection, mul_neg, Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [leviCivita_torsion_free g symmetric 0 i b c]
    ring
  unfold normalizingCoordinateMap
  rw [c2_quadratic_identity_metric_pullback_partial g smooth _
    (normalCoordinateCorrection_symmetric g symmetric) a b c, h1, h2, hc]
  ring

theorem c2_normalizing_metric_germ (g : MetricField) (symmetric : MetricFieldSymmetric g)
    (smooth : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) 0) (value : g 0 = metric) :
    C2NormalizedMetricGerm (coordinateMetricPullback g (normalizingCoordinateMap g)) := by
  refine ⟨coordinateMetricPullback_symmetric g symmetric _, ?_, ?_, ?_⟩
  · intro a b
    apply c2_coordinateMetricPullback_contDiffAt g (normalizingCoordinateMap g) 0
      (normalizingCoordinateMap_local_chart g).1
    simpa only [normalizingCoordinateMap_zero] using smooth
  · rw [normalizingCoordinateMap, quadraticIdentityMap,
      quadratic_metric_pullback_value _ _ _ _ (normalCoordinateCorrection_symmetric g symmetric),
      coordinateFrameMatrix_refl, Matrix.transpose_one, one_mul, mul_one, value]
  · intro a b
    apply continuousLinearMap_zero_of_coordinate_basis
    intro c
    exact c2_normalizing_metric_partial_zero g symmetric smooth value a b c

theorem c2_framedMetricField_smoothAt (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (smooth : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p) :
    ∀ a b, ContDiffAt ℝ 2 (fun x => framedMetricField g p B x a b) 0 := by
  intro a b
  apply c2_coordinateMetricPullback_contDiffAt g (affineCoordinateMap p B) 0
    (affineCoordinateMap_smooth p B).contDiffAt
  simpa only [affineCoordinateMap_zero] using smooth

theorem c2_pointNormalizedMetric_germ (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g)
    (smooth : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p) (frame : LorentzFrameAt g p B) :
    C2NormalizedMetricGerm (pointNormalizedMetric g p B) :=
  c2_normalizing_metric_germ (framedMetricField g p B) (framedMetricField_symmetric g p B symmetric)
    (c2_framedMetricField_smoothAt g p B smooth) (framedMetricField_value g p B frame)

theorem c2_normalizingCoordinateMap_retraction (g : MetricField) (germ : C2NormalizedMetricGerm g) :
    normalizingCoordinateMap g = (fun x => x) := by
  funext x i
  simp [normalizingCoordinateMap, quadraticIdentityMap, quadraticCoordinateMap,
    normalCoordinateCorrection, c2_normalized_metric_christoffel_zero g germ, quadraticPolynomial]

theorem c2_pointNormalizedMetric_retraction (g : MetricField) (germ : C2NormalizedMetricGerm g) :
    pointNormalizedMetric g 0 (ContinuousLinearEquiv.refl ℝ CoordinatePoint) = g := by
  unfold pointNormalizedMetric framedMetricField
  rw [affineCoordinateMap_origin_refl, coordinateMetricPullback_identity,
    c2_normalizingCoordinateMap_retraction g germ, coordinateMetricPullback_identity]

theorem c2_normalizedMetric_identity_frame (g : MetricField) (germ : C2NormalizedMetricGerm g) :
    LorentzFrameAt g 0 (ContinuousLinearEquiv.refl ℝ CoordinatePoint) := by
  simp [LorentzFrameAt, coordinateFrameMatrix_refl, germ.2.2.1]

def c2_normalChartCurvature (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g)
    (smooth : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p) (frame : LorentzFrameAt g p B) : curvatureSpace :=
  c2NormalizedLeviCivitaCurvature (pointNormalizedMetric g p B)
    (c2_pointNormalizedMetric_germ g p B symmetric smooth frame)

theorem c2_normalChartCurvature_retraction (g : MetricField) (germ : C2NormalizedMetricGerm g) :
    c2_normalChartCurvature g 0 (ContinuousLinearEquiv.refl ℝ CoordinatePoint) germ.1 germ.2.1
      (c2_normalizedMetric_identity_frame g germ) = c2NormalizedLeviCivitaCurvature g germ := by
  apply Subtype.ext
  change loweredConnectionCurvature _ (leviCivitaCoefficients _) 0 = _
  rw [c2_pointNormalizedMetric_retraction g germ]
  rfl

/-- One unique coefficient triple for every smooth point and admitted Lorentz
frame in the coordinate-field envelope. Curvature is the actual connection
curvature in the constructed normal chart. Its transport to a general intrinsic
manifold/source interface is not hidden in this theorem. -/

theorem c2_metric_response_normal_chart_envelope_exhaustion (E : MetricFieldResponse)
    (core : MetricFirstResponseCore E) :
    ∃! coefficients : ℝ × ℝ × ℝ,
      ∀ (g : MetricField) (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
        (symmetric : MetricFieldSymmetric g)
        (smooth : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p) (frame : LorentzFrameAt g p B),
      (coordinateFrameMatrix B).transpose * E g p * coordinateFrameMatrix B =
        coefficients.1 • ricciResponse (c2_normalChartCurvature g p B symmetric smooth frame) +
          coefficients.2.1 • scalarMetricResponse (c2_normalChartCurvature g p B symmetric smooth frame) +
            coefficients.2.2 • metric := by
  obtain ⟨coefficients, h, unique⟩ := c2_actual_normalized_metric_response_exhaustion E core
  refine ⟨coefficients, ?_, ?_⟩
  · intro g p B symmetric smooth frame
    have hc := h (pointNormalizedMetric g p B) (c2_pointNormalizedMetric_germ g p B symmetric smooth frame)
    exact (natural_response_point_normal_chart E core.1 g p B symmetric).symm.trans hc
  · intro other ho
    apply unique other
    intro g germ
    have hh := ho g 0 (ContinuousLinearEquiv.refl ℝ CoordinatePoint) germ.1 germ.2.1
      (c2_normalizedMetric_identity_frame g germ)
    simpa only [coordinateFrameMatrix_refl, Matrix.transpose_one, one_mul, mul_one,
      c2_normalChartCurvature_retraction g germ] using hh

#print axioms c2_coordinateMetricPullback_contDiffAt
#print axioms c2_quadratic_identity_metric_pullback_partial
#print axioms c2_normalizing_metric_partial_zero
#print axioms c2_normalizing_metric_germ
#print axioms c2_framedMetricField_smoothAt
#print axioms c2_pointNormalizedMetric_germ
#print axioms c2_normalizingCoordinateMap_retraction
#print axioms c2_pointNormalizedMetric_retraction
#print axioms c2_normalizedMetric_identity_frame
#print axioms c2_normalChartCurvature_retraction
#print axioms c2_metric_response_normal_chart_envelope_exhaustion
end
end AASCSemanticExhaustion
