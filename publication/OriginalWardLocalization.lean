import OccupiedLieReadings
import OccupiedMetricGerms
import OccupiedFullProfileGerms
import CubicWitnessLorentzFrames

/-! Cutoff localization of the occupied compact Lie comparisons. The candidate
supplies a smooth local tensor operator. Its readout is integrated from its
own raised density; no action or geometric closure field is an input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Filter MeasureTheory TopologicalSpace
open AASCSemanticExhaustion AASCKleinGordon
open AASCMetricityOriginalAssembly AASCMetricityLicensingConstruction
open AASCKleinGordon.CanonicalLicensing
open scoped Topology BigOperators ContDiff

namespace AASCOccupiedProfiles

variable {Ω : Opens CoordinatePoint}

private theorem operandTensorIntegrable (H : AdmittedOperand Ω) (T : MetricField)
    (smooth : SmoothCoordinateMetric T) (i : Fin 10) :
    LocallyIntegrableOn (sourceDensityCoordinates
      (raisedSourceTensorDensity (originalEHActMetric H.val) T) i) (Ω : Set CoordinatePoint) volume :=
  (smooth_raised_components _ T (original_eh_act_metric_smooth H.val) smooth
    (original_eh_act_metric_negative H.val H.property) i).continuous.locallyIntegrable.locallyIntegrableOn _

/-- The ordinary first-variation tensor readout on the occupied metric, with
the same half-pairing and symmetric-component weights as the action. -/
def occupiedTensorReadout (H : AdmittedOperand Ω) (T : MetricField)
    (smooth : SmoothCoordinateMetric T) : MetricSourceProbe Ω →L[ℝ] ℝ :=
  nativeRegularMetricDensity _ (operandTensorIntegrable H T smooth)

theorem occupied_tensor_readout_represents (H : AdmittedOperand Ω) (T : MetricField)
    (smooth : SmoothCoordinateMetric T) :
    RepresentsMetricTensor (originalEHActMetric H.val) T (occupiedTensorReadout H T smooth) := by
  let t := sourceDensityCoordinates (raisedSourceTensorDensity (originalEHActMetric H.val) T)
  let u := fun i => nativeRegularScalarDensity (t i) (operandTensorIntegrable H T smooth i)
  have rep : u = representedMetricSource (occupiedTensorReadout H T smooth) := by
    apply constructed_metric_source_unique
    intro K
    rw [occupiedTensorReadout, native_regular_metric_density_integral]
    unfold metricSourcePairing
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change (1/2 : ℝ) * (symmetricSourceWeight i * (∫ p, t i p * K p i)) =
      (symmetricSourceWeight i / 2) * (∫ p, t i p * K p i)
    ring
  intro i φ
  rw [← rep]
  rfl

/-- The minimal observations needed here are precisely the original action
derivatives on compact Lie tests. Only smoothness and symmetry of the rival
tensor are used to turn its response on an operand into its regular readout. -/
def AllOriginalLieReadings (Ω : Opens CoordinatePoint) (κ Λ : ℝ)
    (E : MetricFieldResponse)
    (smooth : ∀ H : AdmittedOperand Ω, SmoothCoordinateMetric (E (originalEHActMetric H.val))) : Prop :=
  ∀ H : AdmittedOperand Ω, MatchesOriginalLieReadings κ Λ H
    (occupiedTensorReadout H _ (smooth H))

private theorem c3_operand_of_same_normal_germ (H : AdmittedOperand Ω) (g : MetricField)
    (germ : C2NormalizedMetricGerm g) (identical : originalEHActMetric H.val =ᶠ[𝓝 0] g) :
    C3NormalizedMetricGerm (originalEHActMetric H.val) := by
  refine ⟨original_eh_act_metric_symmetric H.val, ?_, identical.eq_of_nhds.trans germ.2.2.1, ?_⟩
  · exact fun a b => (original_eh_act_metric_smooth H.val a b).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr (le_top : (3 : ℕ∞) ≤ ⊤))
  · intro a b
    have coords : (fun x => originalEHActMetric H.val x a b) =ᶠ[𝓝 0] fun x => g x a b :=
      identical.mono (fun x eq => congrArg (fun m : Tensor2 => m a b) eq)
    exact coords.fderiv_eq.trans (germ.2.2.2 a b)

private theorem localized_outputs_agree (H : AdmittedOperand Ω) (E : MetricFieldResponse)
    (locality : SmoothMetricGermLocal E) (g : MetricField) (symmetric : MetricFieldSymmetric g)
    (same : originalEHActMetric H.val =ᶠ[𝓝 0] g) :
    E (originalEHActMetric H.val) =ᶠ[𝓝 0] E g := by
  apply (eventually_eventually_nhds.mpr same).mono
  intro x agreed
  change originalEHActMetric H.val =ᶠ[𝓝 x] g at agreed
  have actual := original_eh_act_metric_lorentz H.val H.property x
  have smoothH := original_eh_act_metric_smooth H.val
  have smoothG (i j : Fin 4) : ContDiffAt ℝ ∞ (fun z => g z i j) x :=
    (smoothH i j).contDiffAt.congr_of_eventuallyEq
      (agreed.symm.mono (fun z h => congrArg (fun M : Tensor2 => M i j) h))
  obtain ⟨B, frame⟩ := actual.2.2
  have sameFrame : LorentzFrameAt g x B := by
    unfold LorentzFrameAt at *
    rw [← agreed.eq_of_nhds]
    exact frame
  have domain : C2LorentzMetricAt g x :=
    ⟨symmetric, fun i j => (smoothG i j).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)), B, sameFrame⟩
  exact locality _ _ x actual domain (fun i j => (smoothH i j).contDiffAt) smoothG agreed

/-- Every globally smooth normalized metric, even when originally unbounded
or degenerate away from the point, has a copy of its germ among the occupied
operands. Matching Lie probes closes the covariant response at the point. -/
theorem original_lie_readings_close_normal_germ (Ω : Opens CoordinatePoint)
    (origin : (0 : CoordinatePoint) ∈ Ω) (κ Λ : ℝ) (hk : κ ≠ 0)
    (E : MetricFieldResponse)
    (locality : SmoothMetricGermLocal E)
    (smooth : ∀ H : AdmittedOperand Ω, SmoothCoordinateMetric (E (originalEHActMetric H.val)))
    (symmetric : ∀ H : AdmittedOperand Ω, MetricFieldSymmetric (E (originalEHActMetric H.val)))
    (reads : AllOriginalLieReadings Ω κ Λ E smooth)
    (g : MetricField) (hg : SmoothCoordinateMetric g) (germ : C2NormalizedMetricGerm g) :
    coordinateDivergence g (E g) 0 = 0 := by
  obtain ⟨H, same⟩ := exists_admitted_operand_eq_germ Ω 0 origin g germ.1 hg germ.2.2.1
  have normal := c3_operand_of_same_normal_germ H g germ same
  have closed := occupied_lie_readings_force_normal_closure κ Λ hk H origin normal _
    (smooth H) (symmetric H) _ (occupied_tensor_readout_represents H _ (smooth H)) (reads H)
  exact (coordinate_divergence_of_equal_germs same (localized_outputs_agree H E locality _ germ.1 same)).symm.trans closed

/-- The normal-germ conclusion also holds for a metric smooth only on a
chart patch. No differentiability outside that open patch is required. -/
theorem original_lie_readings_close_normal_patch (Ω V : Opens CoordinatePoint)
    (origin : (0 : CoordinatePoint) ∈ Ω) (inside : (0 : CoordinatePoint) ∈ V)
    (κ Λ : ℝ) (hk : κ ≠ 0) (E : MetricFieldResponse)
    (locality : SmoothMetricGermLocal E)
    (smooth : ∀ H : AdmittedOperand Ω, SmoothCoordinateMetric (E (originalEHActMetric H.val)))
    (symmetric : ∀ H : AdmittedOperand Ω, MetricFieldSymmetric (E (originalEHActMetric H.val)))
    (reads : AllOriginalLieReadings Ω κ Λ E smooth) (g : MetricField)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) (V : Set CoordinatePoint))
    (germ : C2NormalizedMetricGerm g) : coordinateDivergence g (E g) 0 = 0 := by
  obtain ⟨H, same⟩ := exists_admitted_operand_of_chart_germ Ω V 0 origin inside g
    (fun x _ => germ.1 x) hg germ.2.2.1
  have normal := c3_operand_of_same_normal_germ H g germ same
  have closed := occupied_lie_readings_force_normal_closure κ Λ hk H origin normal _
    (smooth H) (symmetric H) _ (occupied_tensor_readout_represents H _ (smooth H)) (reads H)
  exact (coordinate_divergence_of_equal_germs same
    (localized_outputs_agree H E locality _ germ.1 same)).symm.trans closed

/-- Any actual smooth Lorentzian metric at any framed event is tested in its
native normal chart. The point and Lorentz frame are arbitrary. -/
theorem original_lie_readings_close_every_normal_chart (Ω : Opens CoordinatePoint)
    (origin : (0 : CoordinatePoint) ∈ Ω) (κ Λ : ℝ) (hk : κ ≠ 0)
    (E : MetricFieldResponse)
    (locality : SmoothMetricGermLocal E)
    (smooth : ∀ H : AdmittedOperand Ω, SmoothCoordinateMetric (E (originalEHActMetric H.val)))
    (symmetric : ∀ H : AdmittedOperand Ω, MetricFieldSymmetric (E (originalEHActMetric H.val)))
    (reads : AllOriginalLieReadings Ω κ Λ E smooth)
    (g : MetricField) (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (sg : MetricFieldSymmetric g) (hg : SmoothCoordinateMetric g) (frame : LorentzFrameAt g p B) :
    coordinateDivergence (pointNormalizedMetric g p B) (E (pointNormalizedMetric g p B)) 0 = 0 := by
  have hnormal := c2_pointNormalizedMetric_germ g p B sg
    (fun i j => (hg i j).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) frame
  obtain ⟨H, same⟩ := exists_admitted_operand_eq_normal_chart_germ Ω origin g p B sg hg frame
  have normal := c3_operand_of_same_normal_germ H _ hnormal same
  have closed := occupied_lie_readings_force_normal_closure κ Λ hk H origin normal _
    (smooth H) (symmetric H) _ (occupied_tensor_readout_represents H _ (smooth H)) (reads H)
  exact (coordinate_divergence_of_equal_germs same (localized_outputs_agree H E locality _ hnormal.1 same)).symm.trans closed

/-- The one scalar-gradient witness needed for the Einstein coefficient lock
is a polynomial, so closure on smooth normalized metrics suffices even though
the older coefficient theorem formulates its closure hypothesis on C³ germs. -/
theorem original_lie_readings_close_cubic_witness (Ω : Opens CoordinatePoint)
    (origin : (0 : CoordinatePoint) ∈ Ω) (κ Λ : ℝ) (hk : κ ≠ 0)
    (E : MetricFieldResponse)
    (locality : SmoothMetricGermLocal E)
    (smooth : ∀ H : AdmittedOperand Ω, SmoothCoordinateMetric (E (originalEHActMetric H.val)))
    (symmetric : ∀ H : AdmittedOperand Ω, MetricFieldSymmetric (E (originalEHActMetric H.val)))
    (reads : AllOriginalLieReadings Ω κ Λ E smooth) :
    coordinateDivergence (cubicMetricField scalarGradientWitnessJet)
      (E (cubicMetricField scalarGradientWitnessJet)) 0 = 0 := by
  have germ := cubicMetricField_c3_normalized scalarGradientWitnessJet scalarGradientWitnessJet_metric_symmetry
  apply original_lie_readings_close_normal_germ Ω origin κ Λ hk E locality smooth symmetric reads
    _ _ (c3_normalized_metric_c2 _ germ)
  intro i j
  exact contDiff_const.add ((cubicPolynomial_smooth (scalarGradientWitnessJet i j)).of_le (by simp))

/-- A failure of classical closure in any smooth normalized germ separates
a compact Lie reading of an actually occupied bounded operand. -/
theorem nonclosure_has_occupied_lie_witness (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (origin : (0 : CoordinatePoint) ∈ Ω) (κ Λ : ℝ) (hk : κ ≠ 0)
    (E : MetricFieldResponse)
    (locality : SmoothMetricGermLocal E)
    (smooth : ∀ H : AdmittedOperand Ω, SmoothCoordinateMetric (E (originalEHActMetric H.val)))
    (symmetric : ∀ H : AdmittedOperand Ω, MetricFieldSymmetric (E (originalEHActMetric H.val)))
    (g : MetricField) (hg : SmoothCoordinateMetric g) (germ : C2NormalizedMetricGerm g)
    (fails : coordinateDivergence g (E g) 0 ≠ 0) :
    ∃ (H : AdmittedOperand Ω) (X : CoordinateVectorProbe Ω),
      (originalEHActMetric H.val =ᶠ[𝓝 0] g) ∧
      H ∈ currentOperand a Ω '' canonicalSafeUses (originalMetricTask a s Ω κ Λ) ∧
      (∀ᶠ t : ℝ in 𝓝 0, H.val + t • operandLieTest H X ∈ wickOriginalMetricNeighborhood Ω) ∧
      occupiedTensorReadout H _ (smooth H) (operandLieTest H X) ≠
        deriv (fun t : ℝ => originalEHRelativeAction κ Λ wickNativeFlatMetric
          (H.val + t • operandLieTest H X)) 0 := by
  classical
  obtain ⟨H, same⟩ := exists_admitted_operand_eq_germ Ω 0 origin g germ.1 hg germ.2.2.1
  have bad : ¬ MatchesOriginalLieReadings κ Λ H (occupiedTensorReadout H _ (smooth H)) := by
    intro pass
    have normal := c3_operand_of_same_normal_germ H g germ same
    have closed := occupied_lie_readings_force_normal_closure κ Λ hk H origin normal _
      (smooth H) (symmetric H) _ (occupied_tensor_readout_represents H _ (smooth H)) pass
    exact fails ((coordinate_divergence_of_equal_germs same (localized_outputs_agree H E locality _ germ.1 same)).symm.trans closed)
  unfold MatchesOriginalLieReadings at bad
  rcases Classical.not_forall.mp bad with ⟨X, hx⟩
  exact ⟨H, X, same, (occupied_lie_probe_has_standing a s κ Λ hk H X).1,
    (occupied_lie_probe_has_standing a s κ Λ hk H X).2, hx⟩

end AASCOccupiedProfiles
