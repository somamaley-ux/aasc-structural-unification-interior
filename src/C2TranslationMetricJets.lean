import C2CoordinateCurvatureNaturality

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0
set_option autoImplicit false

theorem translation_vector_hasFDerivAt (p x : CoordinatePoint) :
    HasFDerivAt (fun y : CoordinatePoint => y + p) (ContinuousLinearMap.id ℝ CoordinatePoint) x := by
  simpa only using (hasFDerivAt_id (𝕜 := ℝ) x).add_const p

theorem translation_vector_second_zero (p : CoordinatePoint) :
    fderiv ℝ (fderiv ℝ (fun x : CoordinatePoint => x + p)) 0 = 0 := by
  have h : fderiv ℝ (fun x : CoordinatePoint => x + p) =
      (fun _ : CoordinatePoint => ContinuousLinearMap.id ℝ CoordinatePoint) := by
    funext x
    exact (translation_vector_hasFDerivAt p x).fderiv
  rw [h]
  simp

theorem c2_translated_scalar_first (f : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (regular : ContDiffAt ℝ 2 f p) :
    fderiv ℝ (fun x => f (x + p)) 0 = fderiv ℝ f p := by
  have hf : DifferentiableAt ℝ f ((0 : CoordinatePoint) + p) := by
    simpa only [zero_add] using regular.differentiableAt (by norm_num)
  have hd := hf.hasFDerivAt.comp 0 (translation_vector_hasFDerivAt p 0)
  change HasFDerivAt (fun x => f (x + p))
    ((fderiv ℝ f (0 + p)).comp (ContinuousLinearMap.id ℝ CoordinatePoint)) 0 at hd
  simpa only [zero_add, ContinuousLinearMap.comp_id] using hd.fderiv

theorem c2_translated_scalar_second (f : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (regular : ContDiffAt ℝ 2 f p) (c d : Fin 4) :
    scalarSecondPartial (fun x => f (x + p)) 0 c d = scalarSecondPartial f p c d := by
  have hf : ContDiffAt ℝ 2 f ((0 : CoordinatePoint) + p) := by simpa only [zero_add] using regular
  have hF : ContDiffAt ℝ 2 (fun x : CoordinatePoint => x + p) 0 := by fun_prop
  rw [c2_local_scalarSecondPartial_comp f (fun x => x + p) 0 hf hF,
    zero_add, translation_vector_second_zero, (translation_vector_hasFDerivAt p 0).fderiv]
  simp only [ContinuousLinearMap.zero_apply, map_zero, zero_add, ContinuousLinearMap.id_apply]
  exact (c2_scalarSecondPartial_full_second_derivative f p regular c d).symm

theorem c2_metric_translated_regular (g : MetricField) (p : CoordinatePoint)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p) :
    ∀ a b, ContDiffAt ℝ 2 (fun x => g (x + p) a b) 0 := by
  intro a b
  have hg : ContDiffAt ℝ 2 (fun x => g x a b) ((0 : CoordinatePoint) + p) := by
    simpa only [zero_add] using regular a b
  have hF : ContDiffAt ℝ 2 (fun x : CoordinatePoint => x + p) 0 := by fun_prop
  exact hg.comp 0 hF

theorem c2_coordinate_curvature_translation (g : MetricField) (p : CoordinatePoint)
    (symmetric : MetricFieldSymmetric g) (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (nondegenerate : (g p).det ≠ 0) :
    loweredConnectionCurvature (fun x => g (x + p)) (leviCivitaCoefficients (fun x => g (x + p))) 0 =
      loweredConnectionCurvature g (leviCivitaCoefficients g) p := by
  have symT : MetricFieldSymmetric (fun x => g (x + p)) := fun x a b => symmetric (x + p) a b
  have regT := c2_metric_translated_regular g p regular
  have ndT : ((fun x => g (x + p)) 0).det ≠ 0 := by simpa only [zero_add] using nondegenerate
  have hH : c2MetricHessian (fun x => g (x + p)) 0 symT regT = c2MetricHessian g p symmetric regular := by
    apply Subtype.ext
    funext a b c d
    exact c2_translated_scalar_second _ p (regular a b) c d
  have hl (a b c : Fin 4) : lowerChristoffel (fun x => g (x + p)) 0 a b c = lowerChristoffel g p a b c := by
    simp only [lowerChristoffel, metricPartial, c2_translated_scalar_first _ p (regular _ _)]
  have hu (a b c : Fin 4) : leviCivitaCoefficients (fun x => g (x + p)) 0 a b c =
      leviCivitaCoefficients g p a b c := by
    simp only [leviCivitaCoefficients, zero_add, hl]
  funext a b c d
  rw [c2_general_coordinate_curvature_formula _ 0 symT regT ndT,
    c2_general_coordinate_curvature_formula g p symmetric regular nondegenerate, hH]
  simp only [hl, hu]

#print axioms translation_vector_hasFDerivAt
#print axioms translation_vector_second_zero
#print axioms c2_translated_scalar_first
#print axioms c2_translated_scalar_second
#print axioms c2_metric_translated_regular
#print axioms c2_coordinate_curvature_translation
end
end AASCSemanticExhaustion
