import NativeClockActualActionAttachment

namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open TopologicalSpace
open scoped Topology

def nativeScalarClockGradient (χ : CoordinatePoint → ℝ) (p : CoordinatePoint) (a : Fin 4) : ℝ:=
  scalarPartial χ p a

theorem native_scalar_clock_gradient_continuous (χ : CoordinatePoint → ℝ) (hχ : ContDiff ℝ 2 χ) :
    Continuous (nativeScalarClockGradient χ) := by
  have hd:Continuous (fderiv ℝ χ):=(hχ.fderiv_right (m:=0) (by norm_num)).continuous
  apply continuous_pi
  intro a
  exact hd.clm_apply continuous_const

variable {Ω : Opens CoordinatePoint}

def nativeScalarClockRelativeAction (g : MetricField) (χ : CoordinatePoint → ℝ)
    (μ : ℝ) : MetricSourceProbe Ω → ℝ:=
  nativeActualClockMetricAction g (nativeScalarClockGradient χ) χ μ

def nativeScalarClockMetricLF (g : MetricField) (χ : CoordinatePoint → ℝ) (μ : ℝ)
    (hg : Continuous g) (hχ : ContDiff ℝ 2 χ) (hn : ∀ p∈Ω,(g p).det≠0) :
    MetricSourceProbe Ω →L[ℝ] ℝ :=
  nativeClockMetricLF g (nativeScalarClockGradient χ) χ μ hg
    (native_scalar_clock_gradient_continuous χ hχ) hχ.continuous hn

theorem native_scalar_clock_action_derivative_constructed (g : MetricField)
    (hs : MetricFieldSymmetric g) (χ : CoordinatePoint → ℝ) (μ : ℝ)
    (hg : Continuous g) (hχ : ContDiff ℝ 2 χ) (hn : ∀ p∈Ω,(g p).det≠0)
    (h : MetricSourceProbe Ω) :
    HasDerivAt (fun t:ℝ=>nativeScalarClockRelativeAction g χ μ (t • h))
      (nativeScalarClockMetricLF g χ μ hg hχ hn h) 0 :=
  native_clock_metric_action_hasDerivAt g hs (nativeScalarClockGradient χ) χ μ hg
    (native_scalar_clock_gradient_continuous χ hχ) hχ.continuous hn h

theorem native_scalar_clock_actual_action_source_attachment (g : MetricField)
    (hs : MetricFieldSymmetric g) (χ : CoordinatePoint → ℝ) (μ : ℝ)
    (hg : Continuous g) (hχ : ContDiff ℝ 2 χ) (hn : ∀ p∈Ω,(g p).det≠0) :
    ∃! T:SymmetricSourceComponents Ω,∀ h,
      (1/2:ℝ)*metricSourcePairing T h=nativeActionDirectional (nativeScalarClockRelativeAction g χ μ) h :=
  native_clock_actual_action_unique_source g hs (nativeScalarClockGradient χ) χ μ hg
    (native_scalar_clock_gradient_continuous χ hχ) hχ.continuous hn

#print axioms native_scalar_clock_gradient_continuous
#print axioms native_scalar_clock_action_derivative_constructed
#print axioms native_scalar_clock_actual_action_source_attachment
end
end AASCSemanticExhaustion
