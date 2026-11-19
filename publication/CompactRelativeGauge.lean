import OccupiedLieReadings
import OriginalEHIntegratedTransport

/-! Finite compact re-presentations of an actual bounded EH operand on a
fixed coordinate domain. Both operands are supplied independently. The
regional Jacobian theorem proves the equality of their actual relative action
values, without prescribing that equality or imposing field equations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Filter MeasureTheory TopologicalSpace
open AASCSemanticExhaustion AASCKleinGordon
open scoped Topology ContDiff BigOperators
namespace AASCOccupiedProfiles

variable {Ω : Opens CoordinatePoint}

private theorem operand_density_continuous (κ Λ : ℝ) (H : AdmittedOperand Ω) :
    Continuous (originalEHScalarDensity κ Λ (originalEHActMetric H.val)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hg := original_eh_act_metric_smooth H.val
  have hn := original_eh_act_metric_negative H.val H.property p
  exact ((eh_volume_density_smooth_at _ hg p hn).continuousAt.mul
    ((eh_actual_scalar_curvature_smooth_at _ hg p (ne_of_lt hn)).continuousAt.sub
      continuousAt_const)).div_const _

/-- A supplied smooth self-relabeling on a compact invariant patch leaves
the anchored relative EH action unchanged. The perturbed metric and its
pullback are the compared operands, rather than two independently changed
background/test pairs. The bound is used only for the two actual operands.
No finiteness of their absolute actions on the entire domain is required. -/
theorem compact_pullback_preserves_occupied_action (κ Λ : ℝ) (hk : κ ≠ 0)
    (H H' : AdmittedOperand Ω) (s : Set CoordinatePoint) (compact : IsCompact s)
    (inside : s ⊆ (Ω : Set CoordinatePoint)) (support : tsupport (H'.val - H.val) ⊆ s)
    (F : CoordinatePoint → CoordinatePoint) (stable : F '' s = s) (inj : Set.InjOn F s)
    (B : CoordinatePoint → CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (dF : ∀ x ∈ s, HasFDerivAt F (B x).toContinuousLinearMap x)
    (smoothF : ∀ x ∈ s, ContDiffAt ℝ 3 F x)
    (pullback : originalEHActMetric H'.val = coordinateMetricPullback (originalEHActMetric H.val) F) :
    originalEHRelativeAction κ Λ wickNativeFlatMetric H'.val =
      originalEHRelativeAction κ Λ wickNativeFlatMetric H.val := by
  let g := originalEHActMetric H.val
  let g' := originalEHActMetric H'.val
  let K := H'.val - H.val
  have next : H.val + K = H'.val := by dsimp [K]; abel
  have shape : originalEHMetricPerturbation g K = g' := by
    rw [original_eh_act_additive_perturbation, next]
  let L := originalEHScalarDensity κ Λ g
  let L' := originalEHScalarDensity κ Λ g'
  have equalIntegrals : (∫ x in s, L x) = ∫ x in s, L' x := by
    calc
      (∫ x in s, L x) = ∫ x in F '' s, L x := by rw [stable]
      _ = ∫ x in s, |(B x).toContinuousLinearMap.det| • L (F x) := by
        exact integral_image_eq_integral_abs_det_fderiv_smul volume compact.measurableSet
          (fun x hx => (dF x hx).hasFDerivWithinAt) inj L
      _ = ∫ x in s, L' x := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem compact.measurableSet] with p hp
        change _ = originalEHScalarDensity κ Λ (originalEHActMetric H'.val) p
        rw [pullback, original_eh_density_natural κ Λ g (original_eh_act_metric_symmetric H.val)
          F p (fun i j => (original_eh_act_metric_smooth H.val i j).contDiffAt.of_le
            (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
          (ne_of_lt (original_eh_act_metric_negative H.val H.property (F p))) (smoothF p hp)
          (B p) (dF p hp), original_eh_jacobian_det F p (B p) (dF p hp)]
        rfl
  have outside (p : CoordinatePoint) (hp : p ∉ s) : L' p - L p = 0 := by
    have hz := eh_probe_metric_zero_near_outside_support K p (fun h => hp (support h))
    apply sub_eq_zero.mpr
    apply eh_density_congr_of_eventuallyEq
    rw [← shape]
    filter_upwards [hz] with x eq
    change ehProbeMetric K x = 0 at eq
    change g x + ehProbeMetric K x = g x
    rw [eq, add_zero]
  have restricted : (∫ x in (Ω : Set CoordinatePoint), L' x - L x) =
      ∫ x in s, L' x - L x := by
    rw [← integral_indicator Ω.isOpen.measurableSet, ← integral_indicator compact.measurableSet]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem (inside hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      by_cases hΩ : x ∈ Ω
      · rw [Set.indicator_of_mem hΩ]
        exact outside x hx
      · rw [Set.indicator_of_notMem hΩ]
  have zero : originalEHRelativeAction κ Λ g K = 0 := by
    unfold originalEHRelativeAction originalEHRelativeIntegrand
    rw [shape]
    change (∫ x in (Ω : Set CoordinatePoint), L' x - L x) = 0
    rw [restricted, integral_sub ((operand_density_continuous κ Λ H').continuousOn.integrableOn_compact compact)
      ((operand_density_continuous κ Λ H).continuousOn.integrableOn_compact compact), equalIntegrals, sub_self]
  have cocycle := original_eh_action_cocycle κ Λ hk H.val K H.property (next ▸ H'.property)
  rw [next] at cocycle
  exact sub_eq_zero.mp (cocycle.symm.trans zero)

/-- Geometric data for a compactly supported change of presentation of the
actual admitted operand. Its definition contains no metric-action reading. -/
def OccupiedCompactPullback (H H' : AdmittedOperand Ω) : Prop :=
  ∃ (s : Set CoordinatePoint) (F : CoordinatePoint → CoordinatePoint)
    (B : CoordinatePoint → CoordinatePoint ≃L[ℝ] CoordinatePoint),
    IsCompact s ∧ s ⊆ (Ω : Set CoordinatePoint) ∧ tsupport (H'.val - H.val) ⊆ s ∧
    F '' s = s ∧ Set.InjOn F s ∧
    (∀ x ∈ s, HasFDerivAt F (B x).toContinuousLinearMap x) ∧
    (∀ x ∈ s, ContDiffAt ℝ 3 F x) ∧
    originalEHActMetric H'.val = coordinateMetricPullback (originalEHActMetric H.val) F

/-- The actual action along any such curve has derivative zero. Constructing
the required compact flow with a prescribed generator and identifying its
tangent with the ordinary straight Lie probe are separate obligations. -/
theorem compact_pullback_curve_has_zero_action_derivative (κ Λ : ℝ) (hk : κ ≠ 0)
    (H : AdmittedOperand Ω) (curve : ℝ → AdmittedOperand Ω)
    (relabels : ∀ᶠ t : ℝ in 𝓝 0, OccupiedCompactPullback H (curve t)) :
    HasDerivAt (fun t => originalEHRelativeAction κ Λ wickNativeFlatMetric (curve t).val) 0 0 := by
  apply (hasDerivAt_const (0 : ℝ) (originalEHRelativeAction κ Λ wickNativeFlatMetric H.val)).congr_of_eventuallyEq
  filter_upwards [relabels] with t ht
  obtain ⟨s, F, B, compact, inside, support, stable, inj, dF, smoothF, pullback⟩ := ht
  exact compact_pullback_preserves_occupied_action κ Λ hk H (curve t)
    s compact inside support F stable inj B dF smoothF pullback

end AASCOccupiedProfiles
