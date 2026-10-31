import OriginalEHCurvatureVariation

/-! A finite two-jet expression for the same source density. This is not a
new action chosen to fit a response: equality with the independently defined
actual scalar density follows from the proved general-coordinate formula. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Elementwise

abbrev EHMetricJet := Tensor2 × ((Fin 4 → Fin 4 → Fin 4 → ℝ) × Tensor4)

def ehJetFirstEntry (a b c : Fin 4) : EHMetricJet →L[ℝ] ℝ :=
  ({ toFun := fun J => J.2.1 a b c
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : EHMetricJet →ₗ[ℝ] ℝ).toContinuousLinearMap

def ehJetSecondEntry (a b c d : Fin 4) : EHMetricJet →L[ℝ] ℝ :=
  ({ toFun := fun J => J.2.2 a b c d
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : EHMetricJet →ₗ[ℝ] ℝ).toContinuousLinearMap

def ehActualMetricJet (g : MetricField) (p : CoordinatePoint) : EHMetricJet :=
  (g p, (fun a b c => metricPartial g p a b c,
    fun a b c d => scalarSecondPartial (fun x => g x a b) p c d))

def ehJetLowerChristoffel (J : EHMetricJet) (a b c : Fin 4) : ℝ :=
  (1/2 : ℝ) * (J.2.1 a c b + J.2.1 a b c - J.2.1 b c a)

def ehJetLC (J : EHMetricJet) (a b c : Fin 4) : ℝ :=
  ∑ d : Fin 4, J.1⁻¹ a d * ehJetLowerChristoffel J d b c

def ehJetLoweredCurvature (J : EHMetricJet) (a b c d : Fin 4) : ℝ :=
  curvatureOfNormalHessian J.2.2 a b c d +
    (∑ k : Fin 4, ehJetLC J k a d * ehJetLowerChristoffel J k b c) -
    (∑ k : Fin 4, ehJetLC J k a c * ehJetLowerChristoffel J k b d)

def ehJetScalarCurvature (J : EHMetricJet) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, J.1⁻¹ a b *
    (∑ i : Fin 4, ∑ j : Fin 4, J.1⁻¹ i j * ehJetLoweredCurvature J i a j b)

def ehJetDensity (κ Λ : ℝ) (J : EHMetricJet) : ℝ :=
  Real.sqrt (-J.1.det) * (ehJetScalarCurvature J - 2*Λ) / (2*κ)

theorem eh_actual_metric_jet_ray (g h : MetricField) (p : CoordinatePoint)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun x => h x a b) p) (t : ℝ) :
    ehActualMetricJet (ehMetricRay g h t) p =
      ehActualMetricJet g p + t • ehActualMetricJet h p := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext a b c
      exact eh_metric_partial_ray g h p hg hh t a b c
    · funext a b c d
      exact eh_metric_second_partial_ray g h p hg hh t a b c d

theorem eh_jet_scalar_is_actual (g : MetricField) (p : CoordinatePoint)
    (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (hn : (g p).det ≠ 0) :
    ehJetScalarCurvature (ehActualMetricJet g p) = coordinateScalarCurvature g p := by
  unfold coordinateScalarCurvature coordinateRicci
  simp_rw [c2_general_coordinate_curvature_formula g p sg hg hn]
  rfl

theorem eh_jet_density_is_actual (κ Λ : ℝ) (g : MetricField) (p : CoordinatePoint)
    (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (hn : (g p).det ≠ 0) :
    ehJetDensity κ Λ (ehActualMetricJet g p) = originalEHScalarDensity κ Λ g p := by
  rw [ehJetDensity,eh_jet_scalar_is_actual g p sg hg hn]
  rfl

theorem eh_jet_determinant_contDiff : ContDiff ℝ ⊤ (fun J : EHMetricJet => J.1.det) := by
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro j _
  exact (nativeRealMatrixEntry (σ j) j).contDiff.comp contDiff_fst

theorem eh_jet_inverse_entry_contDiffAt (J : EHMetricJet) (hn : J.1.det ≠ 0) (a b : Fin 4) :
    ContDiffAt ℝ ⊤ (fun K : EHMetricJet => K.1⁻¹ a b) J := by
  have adj : ContDiff ℝ ⊤ (fun K : EHMetricJet => K.1.adjugate a b) := by
    simp only [Matrix.adjugate_apply,Matrix.det_apply',Matrix.updateRow_apply]
    apply ContDiff.sum
    intro σ _
    apply contDiff_const.mul
    apply contDiff_prod
    intro j _
    by_cases hj : σ j = b
    · simp only [hj,ite_true]
      exact contDiff_const
    · simp only [hj,ite_false]
      exact (nativeRealMatrixEntry (σ j) j).contDiff.comp contDiff_fst
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
  exact (eh_jet_determinant_contDiff.contDiffAt.inv hn).mul adj.contDiffAt

theorem eh_jet_density_contDiffAt (κ Λ : ℝ) (J : EHMetricJet) (negative : J.1.det < 0) :
    ContDiffAt ℝ ⊤ (ehJetDensity κ Λ) J := by
  have hie (a b : Fin 4) : ContDiffAt ℝ ⊤ (fun K : EHMetricJet => K.1⁻¹ a b) J :=
    eh_jet_inverse_entry_contDiffAt J (ne_of_lt negative) a b
  have first (a b c : Fin 4) : ContDiffAt ℝ ⊤ (fun K : EHMetricJet => K.2.1 a b c) J :=
    (ehJetFirstEntry a b c).contDiff.contDiffAt
  have second (a b c d : Fin 4) : ContDiffAt ℝ ⊤ (fun K : EHMetricJet => K.2.2 a b c d) J :=
    (ehJetSecondEntry a b c d).contDiff.contDiffAt
  have low (a b c : Fin 4) : ContDiffAt ℝ ⊤ (fun K : EHMetricJet => ehJetLowerChristoffel K a b c) J := by
    exact contDiffAt_const.mul (((first a c b).add (first a b c)).sub (first b c a))
  have lc (a b c : Fin 4) : ContDiffAt ℝ ⊤ (fun K : EHMetricJet => ehJetLC K a b c) J := by
    unfold ehJetLC
    apply ContDiffAt.sum
    intro d _
    exact (hie a d).mul (low d b c)
  have curv (a b c d : Fin 4) : ContDiffAt ℝ ⊤
      (fun K : EHMetricJet => ehJetLoweredCurvature K a b c d) J := by
    have hc : ContDiffAt ℝ ⊤ (fun K : EHMetricJet => curvatureOfNormalHessian K.2.2 a b c d) J :=
      contDiffAt_const.mul ((((second a d b c).add (second b c a d)).sub
        (second a c b d)).sub (second b d a c))
    exact (hc.add (ContDiffAt.sum (fun k _ => (lc k a d).mul (low k b c)))).sub
      (ContDiffAt.sum (fun k _ => (lc k a c).mul (low k b d)))
  have scalar : ContDiffAt ℝ ⊤ ehJetScalarCurvature J := by
    unfold ehJetScalarCurvature
    apply ContDiffAt.sum
    intro a _
    apply ContDiffAt.sum
    intro b _
    apply (hie a b).mul
    apply ContDiffAt.sum
    intro i _
    apply ContDiffAt.sum
    intro j _
    exact (hie i j).mul (curv i a j b)
  have vol : ContDiffAt ℝ ⊤ (fun K : EHMetricJet => Real.sqrt (-K.1.det)) J :=
    (eh_jet_determinant_contDiff.contDiffAt.neg).sqrt (neg_ne_zero.mpr (ne_of_lt negative))
  exact (vol.mul (scalar.sub contDiffAt_const)).div_const (2*κ)

theorem eh_actual_metric_jet_contDiff (g : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b)) :
    ContDiff ℝ ∞ (ehActualMetricJet g) := by
  apply ContDiff.prodMk
  · exact contDiff_pi.mpr (fun a => contDiff_pi.mpr (fun b => hg a b))
  · apply ContDiff.prodMk
    · apply contDiff_pi.mpr
      intro a
      apply contDiff_pi.mpr
      intro b
      apply contDiff_pi.mpr
      intro c
      exact ((hg a b).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    · apply contDiff_pi.mpr
      intro a
      apply contDiff_pi.mpr
      intro b
      apply contDiff_pi.mpr
      intro c
      apply contDiff_pi.mpr
      intro d
      have first : ContDiff ℝ ∞ (fun x => scalarPartial (fun y => g y a b) x c) :=
        ((hg a b).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
      exact (first.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem eh_jet_differential_is_actual_density_variation (κ Λ : ℝ)
    (g h : MetricField) (p : CoordinatePoint)
    (sg : MetricFieldSymmetric g) (sh : MetricFieldSymmetric h)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun x => h x a b) p)
    (negative : (g p).det < 0) :
    fderiv ℝ (ehJetDensity κ Λ) (ehActualMetricJet g p) (ehActualMetricJet h p) =
      ehScalarDensityVariation κ Λ g h p := by
  have hp : HasDerivAt (fun t : ℝ => ehActualMetricJet g p + t • ehActualMetricJet h p)
      (ehActualMetricJet h p) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (ehActualMetricJet h p)).const_add
      (ehActualMetricJet g p)
  have base : ContDiffAt ℝ ⊤ (ehJetDensity κ Λ) (ehActualMetricJet g p + (0 : ℝ) • ehActualMetricJet h p) := by
    simpa using eh_jet_density_contDiffAt κ Λ (ehActualMetricJet g p) negative
  have hd := (base.differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt 0 hp
  simp only [zero_smul,add_zero] at hd
  have same : HasDerivAt (fun t : ℝ => originalEHScalarDensity κ Λ (ehMetricRay g h t) p)
      (fderiv ℝ (ehJetDensity κ Λ) (ehActualMetricJet g p) (ehActualMetricJet h p)) 0 := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [eh_metric_ray_nondegenerate_near g h p (ne_of_lt negative)] with t ht
    simp only [Function.comp_def]
    rw [← eh_actual_metric_jet_ray g h p hg hh]
    exact (eh_jet_density_is_actual κ Λ _ p (eh_metric_ray_symmetric g h sg sh t)
      (eh_metric_ray_regular g h p hg hh t) ht).symm
  exact same.unique (eh_scalar_density_variation κ Λ g h p sg sh hg hh negative)

end
end AASCSemanticExhaustion
