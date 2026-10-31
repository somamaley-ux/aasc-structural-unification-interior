import OriginalEHMetricVariation

/-! Parameter differentiation of the actual general-coordinate curvature.
The computed result is a raw coordinate variation, before the separate
Palatini/divergence simplification and compact integration by parts. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Filter
open scoped Topology BigOperators

def ehHessianCurvature (g : MetricField) (p : CoordinatePoint) : Tensor4 :=
  curvatureOfNormalHessian (fun a b c d => scalarSecondPartial (fun x => g x a b) p c d)

def ehLoweredCurvatureVariation (g h : MetricField) (p : CoordinatePoint) : Tensor4 :=
  fun a b c d => ehHessianCurvature h p a b c d +
    (∑ k : Fin 4, (ehLCVariation g h p k a d * lowerChristoffel g p k b c +
      leviCivitaCoefficients g p k a d * lowerChristoffel h p k b c)) -
    (∑ k : Fin 4, (ehLCVariation g h p k a c * lowerChristoffel g p k b d +
      leviCivitaCoefficients g p k a c * lowerChristoffel h p k b d))

def ehRicciVariation (g h : MetricField) (p : CoordinatePoint) : Tensor2 :=
  fun a b => ∑ i : Fin 4, ∑ j : Fin 4,
    (ehInverseVariation g h p i j *
      loweredConnectionCurvature g (leviCivitaCoefficients g) p i a j b +
    (g p)⁻¹ i j * ehLoweredCurvatureVariation g h p i a j b)

def ehScalarCurvatureVariation (g h : MetricField) (p : CoordinatePoint) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4,
    (ehInverseVariation g h p a b * coordinateRicci g p a b +
      (g p)⁻¹ a b * ehRicciVariation g h p a b)

def ehScalarDensityVariation (κ Λ : ℝ) (g h : MetricField) (p : CoordinatePoint) : ℝ :=
  (coordinateVolumeDensity g p * ehScalarCurvatureVariation g h p +
    ((1/2 : ℝ) * coordinateVolumeDensity g p * Matrix.trace ((g p)⁻¹ * h p)) *
      (coordinateScalarCurvature g p - 2*Λ)) / (2*κ)

theorem eh_metric_ray_nondegenerate_near (g h : MetricField) (p : CoordinatePoint)
    (hn : (g p).det ≠ 0) : ∀ᶠ t : ℝ in 𝓝 0, (ehMetricRay g h t p).det ≠ 0 := by
  have hd := native_real_metric_determinant_path_hasDerivAt (g p) (g p)⁻¹ (h p)
    (Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hn))
  have near := hd.continuousAt.tendsto.eventually (isOpen_ne.mem_nhds (by simpa using hn))
  exact near

theorem eh_hessian_curvature_ray (g h : MetricField) (p : CoordinatePoint)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun x => h x a b) p)
    (t : ℝ) (a b c d : Fin 4) :
    ehHessianCurvature (ehMetricRay g h t) p a b c d =
      ehHessianCurvature g p a b c d + t * ehHessianCurvature h p a b c d := by
  simp only [ehHessianCurvature,curvatureOfNormalHessian,
    eh_metric_second_partial_ray g h p hg hh]
  ring

theorem eh_lowered_curvature_variation (g h : MetricField) (p : CoordinatePoint)
    (sg : MetricFieldSymmetric g) (sh : MetricFieldSymmetric h)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun x => h x a b) p)
    (hn : (g p).det ≠ 0) (a b c d : Fin 4) :
    HasDerivAt (fun t : ℝ => loweredConnectionCurvature (ehMetricRay g h t)
      (leviCivitaCoefficients (ehMetricRay g h t)) p a b c d)
      (ehLoweredCurvatureVariation g h p a b c d) 0 := by
  have hH : HasDerivAt (fun t : ℝ => ehHessianCurvature (ehMetricRay g h t) p a b c d)
      (ehHessianCurvature h p a b c d) 0 := by
    simp_rw [eh_hessian_curvature_ray g h p hg hh]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const
      (ehHessianCurvature h p a b c d)).const_add (ehHessianCurvature g p a b c d)
  have hplus := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    (eh_levi_civita_variation g h p hg hh hn k a d).mul
      (eh_lower_christoffel_variation g h p hg hh k b c))
  have hminus := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    (eh_levi_civita_variation g h p hg hh hn k a c).mul
      (eh_lower_christoffel_variation g h p hg hh k b d))
  have result := (hH.add hplus).sub hminus
  simp only [eh_metric_ray_zero] at result
  apply result.congr_of_eventuallyEq
  filter_upwards [eh_metric_ray_nondegenerate_near g h p hn] with t ht
  exact c2_general_coordinate_curvature_formula (ehMetricRay g h t) p
    (eh_metric_ray_symmetric g h sg sh t) (eh_metric_ray_regular g h p hg hh t) ht a b c d

theorem eh_ricci_variation (g h : MetricField) (p : CoordinatePoint)
    (sg : MetricFieldSymmetric g) (sh : MetricFieldSymmetric h)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun x => h x a b) p)
    (hn : (g p).det ≠ 0) (a b : Fin 4) :
    HasDerivAt (fun t : ℝ => coordinateRicci (ehMetricRay g h t) p a b)
      (ehRicciVariation g h p a b) 0 := by
  have result := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      (eh_inverse_entry_variation g h p hn i j).mul
        (eh_lowered_curvature_variation g h p sg sh hg hh hn i a j b)))
  simpa only [coordinateRicci,ehRicciVariation,eh_metric_ray_zero] using result

theorem eh_scalar_curvature_variation (g h : MetricField) (p : CoordinatePoint)
    (sg : MetricFieldSymmetric g) (sh : MetricFieldSymmetric h)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun x => h x a b) p)
    (hn : (g p).det ≠ 0) :
    HasDerivAt (fun t : ℝ => coordinateScalarCurvature (ehMetricRay g h t) p)
      (ehScalarCurvatureVariation g h p) 0 := by
  have result := HasDerivAt.fun_sum (u := Finset.univ) (fun a _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun b _ =>
      (eh_inverse_entry_variation g h p hn a b).mul
        (eh_ricci_variation g h p sg sh hg hh hn a b)))
  simpa only [coordinateScalarCurvature,ehScalarCurvatureVariation,eh_metric_ray_zero] using result

theorem eh_scalar_density_variation (κ Λ : ℝ) (g h : MetricField) (p : CoordinatePoint)
    (sg : MetricFieldSymmetric g) (sh : MetricFieldSymmetric h)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun x => h x a b) p)
    (negative : (g p).det < 0) :
    HasDerivAt (fun t : ℝ => originalEHScalarDensity κ Λ (ehMetricRay g h t) p)
      (ehScalarDensityVariation κ Λ g h p) 0 := by
  have vol := original_eh_lorentz_volume_variation (g p) (h p) negative
  have curv := (eh_scalar_curvature_variation g h p sg sh hg hh (ne_of_lt negative)).sub_const (2*Λ)
  have result := (vol.mul curv).div_const (2*κ)
  convert result using 1
  simp only [ehScalarDensityVariation,coordinateVolumeDensity,
    eh_metric_ray_zero,zero_smul,add_zero]
  ring

end
end AASCSemanticExhaustion
