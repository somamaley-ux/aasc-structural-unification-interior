import OriginalEinsteinHilbertAction

/-! Actual parameter calculus for the independently fixed gravitational action.
No response tensor or Palatini identity is input. The same metric ray is used
for the inverse, spatial jets and Levi-Civita coefficients. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Filter
open scoped Topology BigOperators

def ehMetricRay (g h : MetricField) (t : ℝ) : MetricField :=
  fun p a b => g p a b + t * h p a b

theorem eh_metric_ray_zero (g h : MetricField) : ehMetricRay g h 0 = g := by
  funext p a b
  simp [ehMetricRay]

theorem eh_metric_ray_value (g h : MetricField) (t : ℝ) (p : CoordinatePoint) :
    ehMetricRay g h t p = g p + t • h p := rfl

theorem eh_metric_ray_symmetric (g h : MetricField)
    (hg : MetricFieldSymmetric g) (hh : MetricFieldSymmetric h) (t : ℝ) :
    MetricFieldSymmetric (ehMetricRay g h t) := by
  intro p a b
  simp only [ehMetricRay,hg p a b,hh p a b]

theorem eh_metric_ray_regular (g h : MetricField) (p : CoordinatePoint)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun x => h x a b) p) (t : ℝ) :
    ∀ a b, ContDiffAt ℝ 2 (fun x => ehMetricRay g h t x a b) p :=
  fun a b => (hg a b).add (contDiffAt_const.mul (hh a b))

theorem eh_scalar_second_partial_add (f k : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (hf : ContDiffAt ℝ 2 f p) (hk : ContDiffAt ℝ 2 k p) (c d : Fin 4) :
    scalarSecondPartial (fun x => f x + k x) p c d =
      scalarSecondPartial f p c d + scalarSecondPartial k p c d := by
  rw [c2_scalarSecondPartial_full_second_derivative _ p (hf.add hk)]
  have near : ∀ᶠ x in 𝓝 p,
      fderiv ℝ (fun y => f y + k y) x = fderiv ℝ f x + fderiv ℝ k x := by
    filter_upwards [hf.eventually (by norm_num),hk.eventually (by norm_num)] with x hfx hkx
    exact ((hfx.differentiableAt (by norm_num)).hasFDerivAt.add
      (hkx.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  rw [Filter.EventuallyEq.fderiv_eq near]
  have hd := (((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by simp)).hasFDerivAt.add
    ((hk.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt).fderiv
  change fderiv ℝ (fun x => fderiv ℝ f x + fderiv ℝ k x) p = _ at hd
  rw [hd]
  simp only [ContinuousLinearMap.add_apply]
  rw [c2_scalarSecondPartial_full_second_derivative f p hf,
    c2_scalarSecondPartial_full_second_derivative k p hk]

theorem eh_metric_partial_ray (g h : MetricField) (p : CoordinatePoint)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun x => h x a b) p)
    (t : ℝ) (a b c : Fin 4) :
    metricPartial (ehMetricRay g h t) p a b c =
      metricPartial g p a b c + t * metricPartial h p a b c := by
  unfold metricPartial ehMetricRay
  have hd := (((hg a b).differentiableAt (by norm_num)).hasFDerivAt.add
    (((hh a b).differentiableAt (by norm_num)).hasFDerivAt.const_mul t)).fderiv
  change fderiv ℝ (fun y => g y a b + t * h y a b) p = _ at hd
  rw [hd]
  simp

theorem eh_metric_second_partial_ray (g h : MetricField) (p : CoordinatePoint)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun x => h x a b) p)
    (t : ℝ) (a b c d : Fin 4) :
    scalarSecondPartial (fun x => ehMetricRay g h t x a b) p c d =
      scalarSecondPartial (fun x => g x a b) p c d +
        t * scalarSecondPartial (fun x => h x a b) p c d := by
  unfold ehMetricRay
  rw [eh_scalar_second_partial_add _ _ p (hg a b) (contDiffAt_const.mul (hh a b)),
    c2_local_scalarSecondPartial_const_mul t _ p (hh a b)]

theorem eh_lower_christoffel_ray (g h : MetricField) (p : CoordinatePoint)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun x => h x a b) p)
    (t : ℝ) (a b c : Fin 4) :
    lowerChristoffel (ehMetricRay g h t) p a b c =
      lowerChristoffel g p a b c + t * lowerChristoffel h p a b c := by
  simp only [lowerChristoffel,eh_metric_partial_ray g h p hg hh]
  ring

def ehInverseVariation (g h : MetricField) (p : CoordinatePoint) : Tensor2 :=
  -(g p)⁻¹ * h p * (g p)⁻¹

def ehLCVariation (g h : MetricField) : ConnectionCoefficients := fun p a b c =>
  ∑ d : Fin 4, (ehInverseVariation g h p a d * lowerChristoffel g p d b c +
    (g p)⁻¹ a d * lowerChristoffel h p d b c)

theorem eh_inverse_entry_variation (g h : MetricField) (p : CoordinatePoint)
    (hn : (g p).det ≠ 0) (a b : Fin 4) :
    HasDerivAt (fun t : ℝ => (ehMetricRay g h t p)⁻¹ a b)
      (ehInverseVariation g h p a b) 0 := by
  exact native_real_metric_inverse_entry_hasDerivAt (g p) (g p)⁻¹ (h p)
    (Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hn))
    (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hn)) a b

theorem eh_lower_christoffel_variation (g h : MetricField) (p : CoordinatePoint)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun x => h x a b) p) (a b c : Fin 4) :
    HasDerivAt (fun t : ℝ => lowerChristoffel (ehMetricRay g h t) p a b c)
      (lowerChristoffel h p a b c) 0 := by
  simp_rw [eh_lower_christoffel_ray g h p hg hh]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const
    (lowerChristoffel h p a b c)).const_add (lowerChristoffel g p a b c)

theorem eh_levi_civita_variation (g h : MetricField) (p : CoordinatePoint)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun x => h x a b) p)
    (hn : (g p).det ≠ 0) (a b c : Fin 4) :
    HasDerivAt (fun t : ℝ => leviCivitaCoefficients (ehMetricRay g h t) p a b c)
      (ehLCVariation g h p a b c) 0 := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun d _ =>
    (eh_inverse_entry_variation g h p hn a d).mul
      (eh_lower_christoffel_variation g h p hg hh d b c))
  simpa only [leviCivitaCoefficients,ehLCVariation,eh_metric_ray_zero] using hd

end
end AASCSemanticExhaustion
