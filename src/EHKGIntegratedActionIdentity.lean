import EHKGSecantActionBoundary
import NativeClockDensityContinuity
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Actual integrals of the same scalar densities on arbitrary compact
subdomains of the protected diamond. The divergence term is retained, never
discarded as though the diamond had a fixed spatial boundary. This does not
yet assert a field-variation/stationarity theorem. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open scoped Topology BigOperators
namespace AASCKleinGordon.CurvedKG

theorem local_smooth_gradient_continuous (D : Opens CoordinatePoint)
    (u : CoordinatePoint → ℝ) (regular : ContDiffOn ℝ (⊤ : ℕ∞) u D) :
    ContinuousOn (fun p => scalarPartial u p) D := by
  have first := regular.continuousOn_fderiv_of_isOpen D.isOpen (by exact_mod_cast (show (1 : ℕ∞) ≤ ⊤ from le_top))
  apply continuousOn_pi.mpr
  intro c
  exact first.clm_apply continuousOn_const

theorem local_scalar_density_continuous (D : Opens CoordinatePoint)
    (g : MetricField) (metricContinuous : ContinuousOn g D)
    (nondegenerate : ∀ p ∈ D, (g p).det ≠ 0)
    (u : CoordinatePoint → ℝ) (regular : ContDiffOn ℝ (⊤ : ℕ∞) u D) (mu2 : ℝ) :
    ContinuousOn (fun p => nativeRealClockDensity (g p) (scalarPartial u p) (u p) mu2) D := by
  have gradient := local_smooth_gradient_continuous D u regular
  intro p hp
  exact (native_clock_density_continuousAt g (fun q => scalarPartial u q) u mu2
    ((metricContinuous p hp).continuousAt (D.isOpen.mem_nhds hp))
    ((gradient p hp).continuousAt (D.isOpen.mem_nhds hp))
    ((regular.continuousOn p hp).continuousAt (D.isOpen.mem_nhds hp))
    (nondegenerate p hp)).continuousWithinAt

theorem same_eh_scalar_density_continuous (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiffOn ℝ (⊤ : ℕ∞) u (protectedDiamond (conformalFrequency a))) :
    ContinuousOn (sameEHScalarDensity a u) (protectedDiamond (conformalFrequency a)) := by
  have metricContinuous : Continuous (originalEHActMetric (conformalOperand (conformalFrequency a))) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (original_eh_act_metric_smooth _ i j).continuous
  exact local_scalar_density_continuous
    ⟨protectedDiamond (conformalFrequency a), protected_diamond_open _⟩ _ metricContinuous.continuousOn
    (fun p hp => ne_of_lt (original_eh_act_metric_negative _ (protected_same_eh_nonflat a).2.1 p))
    u regular ((massWaveNumber a) ^ 2)

theorem lifted_flat_scalar_density_continuous (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiffOn ℝ (⊤ : ℕ∞) u (protectedDiamond (conformalFrequency a))) :
    ContinuousOn (fun p => nativeRealClockDensity metric
      (scalarPartial (secantLift (conformalFrequency a) u) p)
      (secantLift (conformalFrequency a) u p) (conformalFrequency a ^ 2))
      (protectedDiamond (conformalFrequency a)) := by
  apply local_scalar_density_continuous
    ⟨protectedDiamond (conformalFrequency a), protected_diamond_open _⟩
    (fun _ => metric) continuousOn_const
    (fun p hp => by rw [canonical_lorentz_metric_det]; norm_num)
    (secantLift (conformalFrequency a) u) (secant_lift_regular _ u regular)

theorem scalar_boundary_partial_continuous (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiffOn ℝ (⊤ : ℕ∞) u (protectedDiamond (conformalFrequency a))) :
    ContinuousOn (fun p => scalarPartial (secantBoundaryFlux (conformalFrequency a) u) p 0)
      (protectedDiamond (conformalFrequency a)) := by
  have difference := (continuousOn_const (c := (2 : ℝ))).mul
    ((lifted_flat_scalar_density_continuous a u regular).sub
      (same_eh_scalar_density_continuous a u regular))
  apply (show ContinuousOn (fun p => (2 : ℝ) *
    (nativeRealClockDensity metric (scalarPartial (secantLift (conformalFrequency a) u) p)
      (secantLift (conformalFrequency a) u p) (conformalFrequency a ^ 2) - sameEHScalarDensity a u p))
      (protectedDiamond (conformalFrequency a)) from difference).congr
  intro p hp
  have identity := protected_same_eh_action_density_boundary a u p hp
    ((regular.contDiffAt ((protected_diamond_open _).mem_nhds hp)).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
  linarith

theorem integrated_same_eh_action_density_boundary (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiffOn ℝ (⊤ : ℕ∞) u (protectedDiamond (conformalFrequency a)))
    (K : Compacts CoordinatePoint) (inside : (K : Set CoordinatePoint) ⊆ protectedDiamond (conformalFrequency a)) :
    (∫ p in (K : Set CoordinatePoint), sameEHScalarDensity a u p) =
      (∫ p in (K : Set CoordinatePoint), nativeRealClockDensity metric
        (scalarPartial (secantLift (conformalFrequency a) u) p)
        (secantLift (conformalFrequency a) u p) (conformalFrequency a ^ 2)) -
      (1 / 2 : ℝ) * ∫ p in (K : Set CoordinatePoint),
        scalarPartial (secantBoundaryFlux (conformalFrequency a) u) p 0 := by
  have flatIntegrable : IntegrableOn (fun p => nativeRealClockDensity metric
      (scalarPartial (secantLift (conformalFrequency a) u) p)
      (secantLift (conformalFrequency a) u p) (conformalFrequency a ^ 2)) (K : Set CoordinatePoint) :=
    ContinuousOn.integrableOn_compact K.isCompact ((lifted_flat_scalar_density_continuous a u regular).mono inside)
  have boundaryIntegrable : IntegrableOn (fun p => scalarPartial
      (secantBoundaryFlux (conformalFrequency a) u) p 0) (K : Set CoordinatePoint) :=
    ContinuousOn.integrableOn_compact K.isCompact ((scalar_boundary_partial_continuous a u regular).mono inside)
  calc
    _ = ∫ p in (K : Set CoordinatePoint),
        nativeRealClockDensity metric (scalarPartial (secantLift (conformalFrequency a) u) p)
          (secantLift (conformalFrequency a) u p) (conformalFrequency a ^ 2) -
        (1 / 2 : ℝ) * scalarPartial (secantBoundaryFlux (conformalFrequency a) u) p 0 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem K.isCompact.measurableSet] with p hp
      exact protected_same_eh_action_density_boundary a u p (inside hp)
        ((regular.contDiffAt ((protected_diamond_open _).mem_nhds (inside hp))).of_le
          (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
    _ = _ := by
      rw [integral_sub flatIntegrable (boundaryIntegrable.const_mul (1 / 2 : ℝ)), integral_const_mul]

end AASCKleinGordon.CurvedKG
