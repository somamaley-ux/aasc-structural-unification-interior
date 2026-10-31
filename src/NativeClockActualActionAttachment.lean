import NativeCompactClockIntegral
import NativeClockLFResponse
import NativeActionDirectionalDifferential

/-! Actual relative scalar-clock action → ordinary directional derivative on
every compact metric test → constructed LF response → unique tensor source.
No action derivative, density representation or conservation field is assumed. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open MeasureTheory TopologicalSpace Filter Set
open scoped Topology

variable {Ω : Opens CoordinatePoint}

def nativeActualClockMetricAction (g : MetricField) (v : CoordinatePoint → Fin 4 → ℝ)
    (φ : CoordinatePoint → ℝ) (μ : ℝ) (h : MetricSourceProbe Ω) : ℝ :=
  ∫ p,nativeRealClockDensity (fun a b=>g p a b+tensorEncode (h p) a b) (v p) (φ p) μ-
    nativeRealClockDensity (g p) (v p) (φ p) μ

theorem native_clock_test_matrix_continuous (h : MetricSourceProbe Ω) :
    Continuous (fun p=>tensorEncode (h p)) :=
  tensorEncodeLinear.toContinuousLinearMap.continuous.comp h.contDiff.continuous

theorem native_clock_metric_action_hasDerivAt (g : MetricField)
    (symmetric : MetricFieldSymmetric g) (v : CoordinatePoint → Fin 4 → ℝ)
    (φ : CoordinatePoint → ℝ) (μ : ℝ) (hg : Continuous g) (hv : Continuous v) (hφ : Continuous φ)
    (hn : ∀ p∈Ω,(g p).det≠0) (h : MetricSourceProbe Ω) :
    HasDerivAt (fun t:ℝ=>nativeActualClockMetricAction g v φ μ (t • h))
      (nativeClockMetricLF g v φ μ hg hv hφ hn h) 0 := by
  let K:Set CoordinatePoint:=tsupport h
  have hK:IsCompact K:=h.hasCompactSupport
  letI:CompactSpace K:=isCompact_iff_compactSpace.mp hK
  let m:Measure K:=volume.comap (Subtype.val:K → CoordinatePoint)
  letI:IsFiniteMeasure m:=⟨by
    change volume.comap (Subtype.val:K → CoordinatePoint) univ<⊤
    rw [comap_subtype_coe_apply hK.measurableSet,Set.image_univ,Subtype.range_coe]
    exact hK.measure_lt_top⟩
  have hc:=native_compact_clock_relative_action_hasDerivAt m
    (fun p:K=>g p) (fun p:K=>tensorEncode (h p)) (fun p:K=>v p) (fun p:K=>φ p) μ
    (hg.comp continuous_subtype_val) ((native_clock_test_matrix_continuous h).comp continuous_subtype_val)
    (hv.comp continuous_subtype_val) (hφ.comp continuous_subtype_val)
    (fun p=>hn p (h.tsupport_subset p.property))
  have he0 : tensorEncode (0:Fin 10 → ℝ)=(0:NativeRealMatrix):=tensorEncodeLinear.map_zero
  have hzero (p : CoordinatePoint) (hp:p∉K) : h p=0:=image_eq_zero_of_notMem_tsupport hp
  have hencode (t:ℝ) (p:CoordinatePoint) : tensorEncode ((t • h) p)=t • tensorEncode (h p):=by
    change tensorEncode (t • h p)=t • tensorEncode (h p)
    exact tensorEncodeLinear.map_smul t (h p)
  have hfun (t:ℝ) : (∫ p:K,nativeRealClockDensity (fun a b=>g p a b+t*tensorEncode (h p) a b) (v p) (φ p) μ-
      nativeRealClockDensity (g p) (v p) (φ p) μ ∂m)=
      nativeActualClockMetricAction g v φ μ (t • h) := by
    dsimp only [m]
    rw [integral_subtype_comap hK.measurableSet (fun p:CoordinatePoint=>
      nativeRealClockDensity (fun a b=>g p a b+t*tensorEncode (h p) a b) (v p) (φ p) μ-
        nativeRealClockDensity (g p) (v p) (φ p) μ)]
    unfold nativeActualClockMetricAction
    simp_rw [hencode]
    rw [← integral_indicator hK.measurableSet]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro p
    by_cases hp:p∈K
    · simp [hp]
    · simp [hp,hzero p hp,he0]
  have hout : (∫ p:K,nativeRealClockMetricVariation (g p) (tensorEncode (h p)) (v p) (φ p) μ ∂m)=
      nativeClockMetricLF g v φ μ hg hv hφ hn h := by
    dsimp only [m]
    rw [integral_subtype_comap hK.measurableSet (fun p:CoordinatePoint=>nativeRealClockMetricVariation (g p) (tensorEncode (h p)) (v p) (φ p) μ),native_clock_LF_is_integrated_actual_variation g symmetric]
    rw [← integral_indicator hK.measurableSet]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro p
    by_cases hp:p∈K
    · simp [hp]
    · simp [hp,hzero p hp,nativeRealClockMetricVariation,he0]
  convert hc using 1
  · funext t
    exact (hfun t).symm
  · exact hout.symm

theorem native_clock_actual_directional_is_constructed_LF (g : MetricField)
    (symmetric : MetricFieldSymmetric g) (v : CoordinatePoint → Fin 4 → ℝ)
    (φ : CoordinatePoint → ℝ) (μ : ℝ) (hg : Continuous g) (hv : Continuous v) (hφ : Continuous φ)
    (hn : ∀ p∈Ω,(g p).det≠0) (h : MetricSourceProbe Ω) :
    nativeActionDirectional (nativeActualClockMetricAction g v φ μ) h=
      nativeClockMetricLF g v φ μ hg hv hφ hn h :=
  (native_clock_metric_action_hasDerivAt g symmetric v φ μ hg hv hφ hn h).deriv

theorem native_clock_actual_action_unique_source (g : MetricField)
    (symmetric : MetricFieldSymmetric g) (v : CoordinatePoint → Fin 4 → ℝ)
    (φ : CoordinatePoint → ℝ) (μ : ℝ) (hg : Continuous g) (hv : Continuous v) (hφ : Continuous φ)
    (hn : ∀ p∈Ω,(g p).det≠0) :
    ∃! T:SymmetricSourceComponents Ω,∀ h,
      (1/2:ℝ)*metricSourcePairing T h=nativeActionDirectional (nativeActualClockMetricAction g v φ μ) h := by
  simpa only [native_clock_actual_directional_is_constructed_LF g symmetric v φ μ hg hv hφ hn] using
    constructed_metric_source_exists_unique (nativeClockMetricLF g v φ μ hg hv hφ hn)

#print axioms native_clock_test_matrix_continuous
#print axioms native_clock_metric_action_hasDerivAt
#print axioms native_clock_actual_directional_is_constructed_LF
#print axioms native_clock_actual_action_unique_source
end
end AASCSemanticExhaustion
