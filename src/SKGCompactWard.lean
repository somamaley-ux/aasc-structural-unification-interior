import SKGConformalDensityCurrent

/-! Actual compact-test Ward closure from the constructed density and scalar
equation. Integration by parts is the retained proved distributional pairing. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

def scalarSmoothTwo (u : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ 2 u := regular.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

theorem actual_scalar_source_density_pairing (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ (⊤ : ℕ∞) u) (X : CoordinateVectorProbe (sourceDomain a)) :
    constructedSourceDivergence (sourceDomain a) (sourceMetric a) (source_metric_smooth a)
      (sameActionScalarSource a u (scalarSmoothTwo u regular)) X =
      ∫ p, ∑ e : Fin 4, classicalTensorDensityCurrent (sourceMetric a)
        (raisedSourceTensorDensity (sourceMetric a) (sameSourceStress a u)) p e * X p e := by
  let t : Fin 10 → CoordinatePoint → ℝ := actualSourceDensityCoordinates a u
  have smooth1 (i : Fin 10) : ContDiff ℝ 1 (t i) :=
    (actual_source_density_smooth a u regular i).of_le
      (WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤))
  have represents (i : Fin 10) (psi : ScalarSourceProbe (sourceDomain a)) :
      sameActionScalarSource a u (scalarSmoothTwo u regular) i psi = ∫ p, t i p * psi p :=
    same_action_source_represents_actual_stress a u _ i psi
  have recovered : (fun p i j => t (sourceSymmetricIndex i j) p) =
      raisedSourceTensorDensity (sourceMetric a) (sameSourceStress a u) :=
    source_density_coordinates_recover _
      (raised_source_tensor_density_symmetric _ _ (same_source_stress_symmetric a u))
  let term := fun i j e => regularDensityCurrentTerm (sourceMetric a) t i j e
  have continuousTerm (i j e : Fin 4) : Continuous (term i j e) :=
    regular_density_current_term_continuous _ (source_metric_smooth a) t smooth1 i j e
  have integrableTerm (i j e : Fin 4) : Integrable (fun p => term i j e p * X p e) :=
    regular_source_test_product_integrable (sourceDomain a) _ (continuousTerm i j e)
      (compactVectorComponentCLM (sourceDomain a) e X)
  have grouped : (∫ p, ∑ i : Fin 4, ∑ j : Fin 4, ∑ e : Fin 4, term i j e p * X p e) =
      ∑ i : Fin 4, ∑ j : Fin 4, ∑ e : Fin 4, ∫ p, term i j e p * X p e := by
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum Finset.univ
      (fun j _ => integrable_finset_sum Finset.univ (fun e _ => integrableTerm i j e)))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finset_sum _ (fun j _ => integrable_finset_sum Finset.univ
      (fun e _ => integrableTerm i j e))]
    apply Finset.sum_congr rfl
    intro j _
    exact integral_finset_sum _ (fun e _ => integrableTerm i j e)
  have pointGrouped (p : CoordinatePoint) :
      (∑ i : Fin 4, ∑ j : Fin 4, ∑ e : Fin 4, term i j e p * X p e) =
      ∑ e : Fin 4, classicalTensorDensityCurrent (sourceMetric a)
        (raisedSourceTensorDensity (sourceMetric a) (sameSourceStress a u)) p e * X p e := by
    rw [← recovered]
    change (∑ i : Fin 4, ∑ j : Fin 4, ∑ e : Fin 4, term i j e p * X p e) =
      ∑ e : Fin 4, (∑ i : Fin 4, ∑ j : Fin 4, term i j e p) * X p e
    calc
      _ = ∑ i : Fin 4, ∑ e : Fin 4, ∑ j : Fin 4, term i j e p * X p e := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = ∑ e : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4, term i j e p * X p e := Finset.sum_comm
      _ = _ := by simp only [Finset.sum_mul]
  have result := regular_constructed_source_divergence_pairing (sourceDomain a) (sourceMetric a)
    (source_metric_smooth a) (sameActionScalarSource a u (scalarSmoothTwo u regular)) t smooth1 represents X
  change _ = ∑ i : Fin 4, ∑ j : Fin 4, ∑ e : Fin 4, ∫ p, term i j e p * X p e at result
  rw [← grouped] at result
  exact result.trans (integral_congr_ae (Eventually.of_forall pointGrouped))

theorem actual_scalar_source_off_shell_compact_pairing (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ (⊤ : ℕ∞) u) (X : CoordinateVectorProbe (sourceDomain a)) :
    constructedSourceDivergence (sourceDomain a) (sourceMetric a) (source_metric_smooth a)
      (sameActionScalarSource a u (scalarSmoothTwo u regular)) X =
      ∫ p, ∑ e : Fin 4, sourceFactor a p ^ 2 *
        ((scalarFieldWaveOperator (sourceMetric a) u p - massWaveNumber a ^ 2 * u p) * scalarPartial u p e) * X p e := by
  rw [actual_scalar_source_density_pairing a u regular X]
  apply integral_congr_ae
  exact Eventually.of_forall (fun p => by
    apply Finset.sum_congr rfl
    intro e _
    rw [actual_scalar_source_density_current a u regular p e])

theorem constructed_scalar_source_distribution_closed (a : Parameters) (f h : CurvedCauchyDatum a) :
    constructedSourceDivergence (sourceDomain a) (sourceMetric a) (source_metric_smooth a)
      (sameActionScalarSource a (sourceField a f h) (scalarSmoothTwo _ (source_field_smooth a f h))) = 0 := by
  ext X
  rw [actual_scalar_source_off_shell_compact_pairing a _ (source_field_smooth a f h) X]
  change (∫ p, ∑ e : Fin 4, sourceFactor a p ^ 2 *
    ((scalarFieldWaveOperator (sourceMetric a) (sourceField a f h) p -
      massWaveNumber a ^ 2 * sourceField a f h p) * scalarPartial (sourceField a f h) p e) * X p e) = 0
  apply integral_eq_zero_of_ae
  filter_upwards with p
  by_cases inside : p ∈ sourceDomain a
  · simp only [source_field_equation a f h p inside, sub_self, zero_mul, mul_zero, Finset.sum_const_zero]
    rfl
  · have zeroX : X p = 0 := image_eq_zero_of_notMem_tsupport
      (fun hp => inside (X.tsupport_subset hp))
    simp only [zeroX, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

theorem actual_scalar_compact_ward (a : Parameters) (f h : CurvedCauchyDatum a)
    (X : CoordinateVectorProbe (sourceDomain a)) :
    sameActionScalarMetricLF a (sourceField a f h) (scalarSmoothTwo _ (source_field_smooth a f h))
      (compactMetricLieCLM (sourceDomain a) (sourceMetric a) (source_metric_smooth a) X) = 0 :=
  (constructed_source_closed_ward_iff (sourceDomain a) (sourceMetric a) (source_metric_smooth a)
    (source_metric_symmetric a) _).mpr (constructed_scalar_source_distribution_closed a f h) X

theorem actual_scalar_compact_lie_ray_stationary (a : Parameters) (f h : CurvedCauchyDatum a)
    (X : CoordinateVectorProbe (sourceDomain a)) :
    HasDerivAt (scalarMetricRayAction a (sourceField a f h)
      ⟨compactMetricLieCLM (sourceDomain a) (sourceMetric a) (source_metric_smooth a) X⟩) 0 0 := by
  have result := same_action_scalar_metric_derivative a _ (scalarSmoothTwo _ (source_field_smooth a f h))
    ⟨compactMetricLieCLM (sourceDomain a) (sourceMetric a) (source_metric_smooth a) X⟩
  rw [actual_scalar_compact_ward a f h X] at result
  exact result

end AASCKleinGordon.SameActionSource
