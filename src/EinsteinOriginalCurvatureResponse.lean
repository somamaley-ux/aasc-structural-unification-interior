import GeneralEnvelopeEinsteinClassification

/-! Source-facing S6 adapter for current Einstein Definition 20.3.
Linearity is stated on the actual normalized Levi-Civita curvature, not on
an assumed Ricci expansion, selected contraction syntax, or desired ratio.
The other original response laws remain explicit hypotheses. This module
does not purport to identify the entire prose S1-S18 predicate automatically. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem original_smooth_normalized_is_c2 (g : MetricField)
    (germ : NormalizedSmoothMetricGerm g) : C2NormalizedMetricGerm g :=
  ⟨germ.1,fun i j => (germ.2.1 i j).of_le (by simp),germ.2.2⟩

def originalNormalizedCurvature (g : MetricField) (germ : NormalizedSmoothMetricGerm g) :
    curvatureSpace := c2NormalizedLeviCivitaCurvature g (original_smooth_normalized_is_c2 g germ)

theorem original_normalized_curvature_add (g h k : MetricField)
    (hg : NormalizedSmoothMetricGerm g) (hh : NormalizedSmoothMetricGerm h)
    (hk : NormalizedSmoothMetricGerm k)
    (second : ∀ a b c d,scalarSecondPartial (fun x => k x a b) 0 c d =
      scalarSecondPartial (fun x => g x a b) 0 c d +
        scalarSecondPartial (fun x => h x a b) 0 c d) :
    originalNormalizedCurvature k hk = originalNormalizedCurvature g hg +
      originalNormalizedCurvature h hh := by
  have hessian : c2MetricHessian k 0 hk.1 (original_smooth_normalized_is_c2 k hk).2.1 =
      c2MetricHessian g 0 hg.1 (original_smooth_normalized_is_c2 g hg).2.1 +
        c2MetricHessian h 0 hh.1 (original_smooth_normalized_is_c2 h hh).2.1 := by
    apply Subtype.ext
    funext a b c d
    exact second a b c d
  simp only [originalNormalizedCurvature,c2_normalizedLeviCivitaCurvature_eq_jet,
    c2NormalizedMetricJetCurvature,hessian,map_add]

theorem original_normalized_curvature_smul (r : ℝ) (g k : MetricField)
    (hg : NormalizedSmoothMetricGerm g) (hk : NormalizedSmoothMetricGerm k)
    (second : ∀ a b c d,scalarSecondPartial (fun x => k x a b) 0 c d =
      r * scalarSecondPartial (fun x => g x a b) 0 c d) :
    originalNormalizedCurvature k hk = r • originalNormalizedCurvature g hg := by
  have hessian : c2MetricHessian k 0 hk.1 (original_smooth_normalized_is_c2 k hk).2.1 =
      r • c2MetricHessian g 0 hg.1 (original_smooth_normalized_is_c2 g hg).2.1 := by
    apply Subtype.ext
    funext a b c d
    exact second a b c d
  simp only [originalNormalizedCurvature,c2_normalizedLeviCivitaCurvature_eq_jet,
    c2NormalizedMetricJetCurvature,hessian,map_smul]

/-- Actual curvature first-response law, allowing the homogeneous metric baseline.
No response coefficients or curvature-to-response factorization are supplied. -/
def OriginalCurvatureFirstResponse (E : MetricFieldResponse) : Prop :=
  (∀ g h k : MetricField,∀ hg : NormalizedSmoothMetricGerm g,
    ∀ hh : NormalizedSmoothMetricGerm h,∀ hk : NormalizedSmoothMetricGerm k,
    originalNormalizedCurvature k hk = originalNormalizedCurvature g hg +
      originalNormalizedCurvature h hh → E k 0=E g 0+E h 0-E flatMetricField 0) ∧
  (∀ r : ℝ,∀ g k : MetricField,∀ hg : NormalizedSmoothMetricGerm g,
    ∀ hk : NormalizedSmoothMetricGerm k,
    originalNormalizedCurvature k hk = r • originalNormalizedCurvature g hg →
      E k 0=r • (E g 0-E flatMetricField 0)+E flatMetricField 0)

theorem original_curvature_first_response_derives_metric_affinity
    (E : MetricFieldResponse) (original : OriginalCurvatureFirstResponse E) :
    MetricFirstResponseAffine E := by
  constructor
  · intro g h k hg hh hk second
    exact original.1 g h k hg hh hk (original_normalized_curvature_add g h k hg hh hk second)
  · intro r g k hg hk second
    exact original.2 r g k hg hk (original_normalized_curvature_smul r g k hg hk second)

theorem original_curvature_response_derives_regular_core
    (E : MetricFieldResponse) (natural : RegularLorentzResponseNatural E)
    (locality : RegularLorentzTwoJetLocal E) (original : OriginalCurvatureFirstResponse E)
    (symmetric : ∀ g p,C2LorentzMetricAt g p → ∀ i j,E g p i j=E g p j i) :
    RegularLorentzResponseCore E :=
  ⟨natural,locality,original_curvature_first_response_derives_metric_affinity E original,symmetric⟩

theorem original_curvature_general_response_has_unique_einstein_form
    (E : MetricFieldResponse) (natural : RegularLorentzResponseNatural E)
    (locality : RegularLorentzTwoJetLocal E) (original : OriginalCurvatureFirstResponse E)
    (symmetric : ∀ g p,C2LorentzMetricAt g p → ∀ i j,E g p i j=E g p j i)
    (general_closure : GeneralNormalMetricResponseClosure E)
    (active : FullLorentzEnvelopeResponseActive E) :
    ∃! ac : ℝ × ℝ,ac.1≠0 ∧ CoordinateEinsteinResponseForm E ac.1 ac.2 :=
  regular_general_envelope_unique_einstein_response E
    (original_curvature_response_derives_regular_core E natural locality original symmetric)
    general_closure active

#print axioms original_smooth_normalized_is_c2
#print axioms originalNormalizedCurvature
#print axioms original_normalized_curvature_add
#print axioms original_normalized_curvature_smul
#print axioms OriginalCurvatureFirstResponse
#print axioms original_curvature_first_response_derives_metric_affinity
#print axioms original_curvature_response_derives_regular_core
#print axioms original_curvature_general_response_has_unique_einstein_form
end
end AASCSemanticExhaustion
