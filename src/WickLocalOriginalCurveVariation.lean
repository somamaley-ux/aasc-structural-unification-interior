import WickOriginalCurveVariation
import WickLocalCompactCurveAction

/-! The same original integral and strong source, with regularity required only
on an actual open parameter neighborhood. No global-time regularity is needed. -/
noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology Matrix.Norms.Operator
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem original_wick_native_response_along_local_compact_C1_metric_curve
    (a : Parameters) (s : ℝ) (u v : FiniteParticleCore)
    (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω)
    (γ γdot : ℝ → Spacetime → NativeRealMatrix) (K : Set Spacetime) (hK : IsCompact K)
    (I : Set ℝ) (hI : IsOpen I) (h0 : (0:ℝ)∈I)
    (hγ : ContinuousOn (fun z : ℝ × K => γ z.1 z.2) (I ×ˢ univ))
    (hγdot : ContinuousOn (fun z : ℝ × K => γdot z.1 z.2) (I ×ˢ univ))
    (hderiv : ∀ t∈I,∀ x,HasDerivAt (fun r => γ r x) (γdot t x) t)
    (base : ∀ x,γ 0 x=wickFlatMetric)
    (tangent : ∀ x,γdot 0 x=wickNativeMetricVariation H x)
    (support : ∀ᶠ t in 𝓝 (0:ℝ),∀ x,x∉K → γ t x=wickFlatMetric) :
    HasDerivAt (originalWickCurveRelativeAction a s u v γ)
      (originalWickNativeStrongResponse a s Ω H v u) 0 := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let m : Measure K := volume.comap (Subtype.val : K → Spacetime)
  letI : IsFiniteMeasure m := ⟨by
    change volume.comap (Subtype.val : K → Spacetime) univ < ⊤
    rw [comap_subtype_coe_apply hK.measurableSet,Set.image_univ,Subtype.range_coe]
    exact hK.measure_lt_top⟩
  have hD := original_wick_derivative_components_continuous a s u v
  have hM := original_wick_mass_square_continuous a s u v
  have hn : wickFlatMetric.det≠0 := by rw [wick_flat_metric_det]; norm_num
  have hc := wick_local_compact_quantum_curve_relative_action_hasDerivAt m
    (fun t (x:K) => γ t x) (fun t (x:K) => γdot t x)
    (fun x:K => originalWickDerivativeComponents a s u v x)
    (fun x:K => originalWickMassSquare a s u v x) I hI h0 hγ hγdot
    (fun t ht x => hderiv t ht x) (hD.comp continuous_subtype_val)
    (hM.comp continuous_subtype_val) (fun x => by dsimp only;rw [base];exact hn)
  have hzero : ∀ x,x∉K → wickNativeMetricVariation H x=0 := by
    intro x hx
    rw [← tangent]
    have heq : (fun t => γ t x)=ᶠ[𝓝 (0:ℝ)] (fun _ => wickFlatMetric) :=
      support.mono (fun _ ht => ht x hx)
    exact (hderiv 0 h0 x).unique
      ((hasDerivAt_const (0:ℝ) wickFlatMetric).congr_of_eventuallyEq heq)
  have hfun : originalWickCurveRelativeAction a s u v γ =ᶠ[𝓝 (0:ℝ)]
      (fun t => ∫ x:K,wickQuantumActionDensity (γ t x)
        (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x)-
        wickQuantumActionDensity (γ 0 x)
          (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x) ∂m) := by
    filter_upwards [support] with t ht
    dsimp only [m]
    rw [integral_subtype_comap hK.measurableSet (fun x : Spacetime =>
      wickQuantumActionDensity (γ t x) (originalWickDerivativeComponents a s u v x)
        (originalWickMassSquare a s u v x)-
      wickQuantumActionDensity (γ 0 x) (originalWickDerivativeComponents a s u v x)
        (originalWickMassSquare a s u v x))]
    simp_rw [base]
    unfold originalWickCurveRelativeAction
    rw [← integral_indicator hK.measurableSet]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by
      by_cases hx : x∈K
      · simp [hx]
      · simp [hx,ht x hx])
  have hs := wick_compact_quantum_relative_action_hasDerivAt m
    (fun _:K => wickFlatMetric) (fun x:K => wickNativeMetricVariation H x)
    (fun x:K => originalWickDerivativeComponents a s u v x)
    (fun x:K => originalWickMassSquare a s u v x) continuous_const
    ((wick_native_metric_variation_smooth H).continuous.comp continuous_subtype_val)
    (hD.comp continuous_subtype_val) (hM.comp continuous_subtype_val) (fun _ => hn)
  have hstraight (t:ℝ) : originalWickScalarRelativeAction a s u v (wickNativeMetricVariation H) t =
      ∫ x:K,wickQuantumActionDensity (wickFlatMetric+t • wickNativeMetricVariation H x)
        (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x)-
        wickQuantumActionDensity wickFlatMetric
          (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x) ∂m := by
    dsimp only [m]
    rw [integral_subtype_comap hK.measurableSet (fun x : Spacetime =>
      wickQuantumActionDensity (wickFlatMetric+t • wickNativeMetricVariation H x)
        (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x)-
      wickQuantumActionDensity wickFlatMetric (originalWickDerivativeComponents a s u v x)
        (originalWickMassSquare a s u v x))]
    unfold originalWickScalarRelativeAction
    rw [← integral_indicator hK.measurableSet]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by
      by_cases hx : x∈K
      · simp [hx]
      · simp [hx,hzero x hx])
  have hs' := hs.congr_of_eventuallyEq (Eventually.of_forall hstraight)
  have hvalue := hs'.unique (original_wick_native_strong_response_actual_action_derivative a s Ω H v u)
  have hc' := hc.congr_of_eventuallyEq hfun
  simpa only [base,tangent,hvalue] using hc'

end AASCKleinGordon
