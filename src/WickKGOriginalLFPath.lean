import WickKGOriginalProtocolTransport
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! The protocol curves are C1 in the ORIGINAL LF topology: their actual
difference quotients converge there, and their derivative curve is continuous.
This is stronger than merely proving C1 after evaluating at a spacetime point. -/
noncomputable section
set_option maxHeartbeats 1000000
open Filter TopologicalSpace
open scoped Topology
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickKGOriginalTestPath {Ω : Opens CoordinatePoint} (δ : WickKGFirstMetricAct Ω)
    (t : ℝ) : MetricSourceProbe Ω := δ.parameter t • δ.test

def wickKGOriginalTestVelocity {Ω : Opens CoordinatePoint} (δ : WickKGFirstMetricAct Ω)
    (t : ℝ) : MetricSourceProbe Ω := deriv δ.parameter t • δ.test

theorem wick_scalar_multiple_LF_difference_quotient {Ω : Opens CoordinatePoint}
    (H : MetricSourceProbe Ω) (α : ℝ → ℝ) (t c : ℝ) (derivative : HasDerivAt α c t) :
    Tendsto (fun h : ℝ => h⁻¹ • ((α (t+h) • H)-(α t • H)))
      (𝓝[≠] 0) (𝓝 (c • H)) := by
  have scalar := derivative.tendsto_slope_zero
  have lifted := scalar.smul (tendsto_const_nhds (x:=H))
  simpa only [smul_eq_mul,← sub_smul,smul_smul] using lifted

theorem wick_KG_original_LF_difference_quotient {Ω : Opens CoordinatePoint}
    (δ : WickKGFirstMetricAct Ω) :
    Tendsto (fun h : ℝ => h⁻¹ • (wickKGOriginalTestPath δ h-wickKGOriginalTestPath δ 0))
      (𝓝[≠] 0) (𝓝 (wickKGFirstTangent δ)) := by
  simpa only [zero_add,wickKGOriginalTestPath,wickKGFirstTangent] using
    wick_scalar_multiple_LF_difference_quotient δ.test δ.parameter 0 δ.rate δ.derivative

theorem wick_KG_original_LF_derivative_near {Ω : Opens CoordinatePoint}
    (δ : WickKGFirstMetricAct Ω) :
    ∀ᶠ t in 𝓝 0,Tendsto
      (fun h : ℝ => h⁻¹ • (wickKGOriginalTestPath δ (t+h)-wickKGOriginalTestPath δ t))
      (𝓝[≠] 0) (𝓝 (wickKGOriginalTestVelocity δ t)) := by
  filter_upwards [δ.parameter_C1.eventually (by simp)] with t ht
  exact wick_scalar_multiple_LF_difference_quotient δ.test δ.parameter t (deriv δ.parameter t)
    ht.differentiableAt_one.hasDerivAt

theorem wick_KG_original_LF_velocity_continuous {Ω : Opens CoordinatePoint}
    (δ : WickKGFirstMetricAct Ω) : ContinuousAt (wickKGOriginalTestVelocity δ) 0 := by
  have hd : ContDiffAt ℝ 0 (deriv δ.parameter) 0 := δ.parameter_C1.derivWithin (by norm_num)
  exact hd.continuousAt.smul continuousAt_const

theorem wick_KG_original_LF_velocity_at_zero {Ω : Opens CoordinatePoint}
    (δ : WickKGFirstMetricAct Ω) : wickKGOriginalTestVelocity δ 0=wickKGFirstTangent δ := by
  simp only [wickKGOriginalTestVelocity,δ.derivative.deriv,wickKGFirstTangent]

theorem wick_KG_original_LF_velocity_continuous_near {Ω : Opens CoordinatePoint}
    (δ : WickKGFirstMetricAct Ω) :
    ∀ᶠ t in 𝓝 0,ContinuousAt (wickKGOriginalTestVelocity δ) t := by
  filter_upwards [δ.parameter_C1.eventually (by simp)] with t ht
  have hd : ContDiffAt ℝ 0 (deriv δ.parameter) t := ht.derivWithin (by norm_num)
  exact hd.continuousAt.smul continuousAt_const

theorem wick_KG_original_every_continuous_seminorm_derivative {Ω : Opens CoordinatePoint}
    (δ : WickKGFirstMetricAct Ω) (p : Seminorm ℝ (MetricSourceProbe Ω)) (continuous : Continuous p) :
    Tendsto (fun h : ℝ => p (h⁻¹ •
      (wickKGOriginalTestPath δ h-wickKGOriginalTestPath δ 0)-wickKGFirstTangent δ))
      (𝓝[≠] 0) (𝓝 0) := by
  have h := (wick_KG_original_LF_difference_quotient δ).sub
    (tendsto_const_nhds (x:=wickKGFirstTangent δ))
  have hc := continuous.continuousAt.tendsto.comp h
  simpa only [sub_self,map_zero] using hc

end AASCKleinGordon
