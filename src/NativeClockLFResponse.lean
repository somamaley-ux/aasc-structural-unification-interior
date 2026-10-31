import NativeRegularDensityLF
import NativeRealClockJetAgreement
import NativeClockDensityContinuity
import CompactSourceWardConstruction

namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open MeasureTheory TopologicalSpace
open scoped BigOperators Topology

def nativeClockEntryProbe (a b : Fin 4) : NativeRealMatrix:=fun i j=>if i=a ∧ j=b then 1 else 0

theorem native_trace_entry_probe (A : NativeRealMatrix) (a b : Fin 4) :
    Matrix.trace (A*nativeClockEntryProbe b a)=A a b := by
  simp [Matrix.trace,Matrix.diag,Matrix.mul_apply,nativeClockEntryProbe,mul_ite,ite_and]

def nativeClockSourceCoefficient (g : MetricField) (v : CoordinatePoint → Fin 4 → ℝ)
    (φ : CoordinatePoint → ℝ) (μ : ℝ) (i : Fin 10) (p : CoordinatePoint) : ℝ :=
  nativeRealClockVolume (g p)*tensorDecode ((g p)⁻¹*nativeRealClockStress (g p) (v p) (φ p) μ*(g p)⁻¹) i

theorem native_clock_coefficient_is_computed_variation (g : MetricField)
    (v : CoordinatePoint → Fin 4 → ℝ) (φ : CoordinatePoint → ℝ) (μ : ℝ)
    (i : Fin 10) (p : CoordinatePoint) :
    nativeClockSourceCoefficient g v φ μ i p=
      2*nativeRealClockMetricVariation (g p)
        (nativeClockEntryProbe (sourceSymmetricPair i).2 (sourceSymmetricPair i).1) (v p) (φ p) μ := by
  unfold nativeClockSourceCoefficient nativeRealClockMetricVariation
  rw [native_trace_entry_probe]
  have he : tensorDecode ((g p)⁻¹*nativeRealClockStress (g p) (v p) (φ p) μ*(g p)⁻¹) i=
      ((g p)⁻¹*nativeRealClockStress (g p) (v p) (φ p) μ*(g p)⁻¹) (sourceSymmetricPair i).1 (sourceSymmetricPair i).2 := by
    fin_cases i <;> rfl
  rw [he]
  ring

variable {Ω : Opens CoordinatePoint}

theorem native_clock_source_coefficients_locally_integrable (g : MetricField)
    (v : CoordinatePoint → Fin 4 → ℝ) (φ : CoordinatePoint → ℝ) (μ : ℝ)
    (hg : Continuous g) (hv : Continuous v) (hφ : Continuous φ)
    (hn : ∀ p∈Ω,(g p).det≠0) (i : Fin 10) :
    LocallyIntegrableOn (nativeClockSourceCoefficient g v φ μ i) (Ω:Set CoordinatePoint) volume := by
  apply ContinuousOn.locallyIntegrableOn _ Ω.isOpen.measurableSet
  intro p hp
  have hc:ContinuousAt (fun p=>2*nativeRealClockMetricVariation (g p)
      (nativeClockEntryProbe (sourceSymmetricPair i).2 (sourceSymmetricPair i).1) (v p) (φ p) μ) p :=
    continuousAt_const.mul (native_clock_variation_continuousAt g _ v φ μ hg.continuousAt
      continuousAt_const hv.continuousAt hφ.continuousAt (hn p hp))
  simpa only [← native_clock_coefficient_is_computed_variation] using hc.continuousWithinAt

def nativeClockMetricLF (g : MetricField) (v : CoordinatePoint → Fin 4 → ℝ)
    (φ : CoordinatePoint → ℝ) (μ : ℝ) (hg : Continuous g) (hv : Continuous v) (hφ : Continuous φ)
    (hn : ∀ p∈Ω,(g p).det≠0) : MetricSourceProbe Ω →L[ℝ] ℝ :=
  nativeRegularMetricDensity (nativeClockSourceCoefficient g v φ μ)
    (native_clock_source_coefficients_locally_integrable g v φ μ hg hv hφ hn)

theorem native_clock_raised_stress_symmetric (G : NativeRealMatrix) (hs : G.transpose=G)
    (v : Fin 4 → ℝ) (φ μ : ℝ) :
    (G⁻¹*nativeRealClockStress G v φ μ*G⁻¹).transpose=G⁻¹*nativeRealClockStress G v φ μ*G⁻¹ := by
  have hB:G⁻¹.transpose=G⁻¹:=by rw [Matrix.transpose_nonsing_inv,hs]
  have hT:(nativeRealClockStress G v φ μ).transpose=nativeRealClockStress G v φ μ:=by
    ext a b
    have hh:=congrArg (fun M:NativeRealMatrix=>M a b) hs
    simp only [Matrix.transpose_apply] at hh
    simp [nativeRealClockStress,nativeRealClockOuter,Matrix.transpose_apply,hh]
    ring
  rw [Matrix.transpose_mul,Matrix.transpose_mul,hB,hT]
  simp only [Matrix.mul_assoc]

theorem native_clock_variation_complete_ten_components (g : MetricField)
    (symmetric : MetricFieldSymmetric g) (v : CoordinatePoint → Fin 4 → ℝ)
    (φ : CoordinatePoint → ℝ) (μ : ℝ) (p : CoordinatePoint) (x : Fin 10 → ℝ) :
    nativeRealClockMetricVariation (g p) (tensorEncode x) (v p) (φ p) μ=
      ∑ i,(symmetricSourceWeight i/2)*nativeClockSourceCoefficient g v φ μ i p*x i := by
  have hg:(g p).transpose=g p:=by ext a b; exact symmetric p b a
  have hA:=native_clock_raised_stress_symmetric (g p) hg (v p) (φ p) μ
  have hPair:=symmetric_source_full_matrix_pairing
    (tensorDecode ((g p)⁻¹*nativeRealClockStress (g p) (v p) (φ p) μ*(g p)⁻¹)) x
  rw [tensor_encode_decode _ (by intro a b; exact (congrArg (fun M:NativeRealMatrix=>M b a) hA))] at hPair
  unfold nativeRealClockMetricVariation nativeClockSourceCoefficient
  rw [native_trace_pairing_symmetric _ _ hA,hPair,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem native_clock_LF_is_integrated_actual_variation (g : MetricField)
    (symmetric : MetricFieldSymmetric g) (v : CoordinatePoint → Fin 4 → ℝ)
    (φ : CoordinatePoint → ℝ) (μ : ℝ) (hg : Continuous g) (hv : Continuous v) (hφ : Continuous φ)
    (hn : ∀ p∈Ω,(g p).det≠0) (h : MetricSourceProbe Ω) :
    nativeClockMetricLF g v φ μ hg hv hφ hn h=
      ∫ p,nativeRealClockMetricVariation (g p) (tensorEncode (h p)) (v p) (φ p) μ := by
  rw [nativeClockMetricLF,native_regular_metric_density_integral]
  simp_rw [native_clock_variation_complete_ten_components g symmetric]
  have hint (i : Fin 10) : Integrable (fun p =>
      (symmetricSourceWeight i/2)*nativeClockSourceCoefficient g v φ μ i p*h p i) volume := by
    have hi:=native_locally_integrable_test_product _
      (native_clock_source_coefficients_locally_integrable g v φ μ hg hv hφ hn i) (sourceTestProjection i h)
    simpa [sourceTestProjection,TestFunction.postcompCLM_apply,mul_assoc] using hi.const_mul (symmetricSourceWeight i/2)
  rw [integral_finset_sum _ (fun i _=>hint i)]
  simp_rw [mul_assoc,integral_const_mul]

#print axioms native_trace_entry_probe
#print axioms native_clock_coefficient_is_computed_variation
#print axioms native_clock_source_coefficients_locally_integrable
#print axioms native_clock_raised_stress_symmetric
#print axioms native_clock_variation_complete_ten_components
#print axioms native_clock_LF_is_integrated_actual_variation
end
end AASCSemanticExhaustion
