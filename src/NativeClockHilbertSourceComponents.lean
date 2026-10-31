import NativeScalarClockMetricAction
import NativeActionClassicalSource

/-! The source reconstructed from the actual scalar-clock action has the
computed regular Hilbert density on every compact scalar test. The density
representation is proved here, not received as a field of the native record. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology

variable {Ω : Opens CoordinatePoint}

theorem native_component_functionals_reconstructed
    (D : Fin 10 → ScalarSourceProbe Ω →L[ℝ] ℝ) :
    representedMetricSource (∑ i,(symmetricSourceWeight i/2) • (D i).comp (sourceTestProjection i))=D := by
  funext i
  ext φ
  simp [representedMetricSource,ContinuousLinearMap.sum_apply,
    compact_metric_test_projection_insertion,ContinuousLinearMap.comp_apply]
  simp_rw [apply_ite,map_zero]
  simp
  field_simp [symmetric_source_weight_ne_zero i]

theorem native_clock_constructed_source_integral_components (g : MetricField)
    (v : CoordinatePoint → Fin 4 → ℝ) (φ : CoordinatePoint → ℝ) (μ : ℝ)
    (hg : Continuous g) (hv : Continuous v) (hφ : Continuous φ) (hn : ∀ p∈Ω,(g p).det≠0)
    (i : Fin 10) (ψ : ScalarSourceProbe Ω) :
    representedMetricSource (nativeClockMetricLF g v φ μ hg hv hφ hn) i ψ=
      ∫ p,nativeClockSourceCoefficient g v φ μ i p*ψ p := by
  unfold nativeClockMetricLF nativeRegularMetricDensity
  rw [native_component_functionals_reconstructed]
  rfl

theorem native_lorentz_frame_determinant_negative (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (frame : LorentzFrameAt g p B) :
    (g p).det<0 := by
  have hd:=congrArg Matrix.det frame
  simp only [Matrix.det_mul,Matrix.det_transpose,canonical_lorentz_metric_det] at hd
  by_contra hn
  have hh:=mul_nonneg (le_of_not_gt hn) (sq_nonneg (coordinateFrameMatrix B).det)
  nlinarith

theorem native_raise_source_matrix_identity (B T : NativeRealMatrix) (hs : B.transpose=B)
    (a b : Fin 4) :
    (B*T*B) a b=∑ i,∑ j,B a i*B b j*T i j := by
  simp only [Matrix.mul_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hh:=congrArg (fun M:NativeRealMatrix=>M j b) hs
  simp only [Matrix.transpose_apply] at hh
  rw [← hh]
  ring

theorem native_clock_coefficient_is_actual_raised_density (g : MetricField)
    (hs : MetricFieldSymmetric g) (χ : CoordinatePoint → ℝ) (μ : ℝ)
    (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (frame : LorentzFrameAt g p B) (i : Fin 10) :
    nativeClockSourceCoefficient g (nativeScalarClockGradient χ) χ μ i p=
      sourceDensityCoordinates (raisedSourceTensorDensity g (scalarFieldStress g χ μ)) i p := by
  have hG:(g p).transpose=g p:=by ext a b;exact hs p b a
  have hB:(g p)⁻¹.transpose=(g p)⁻¹:=by rw [Matrix.transpose_nonsing_inv,hG]
  have hT:nativeRealClockStress (g p) (nativeScalarClockGradient χ p) (χ p) μ=scalarFieldStress g χ μ p:=
    native_real_clock_stress_is_actual_scalar_stress g χ p μ
  have hn:=native_lorentz_frame_determinant_negative g p B frame
  unfold nativeClockSourceCoefficient sourceDensityCoordinates raisedSourceTensorDensity
  rw [hT]
  have hdecode: tensorDecode ((g p)⁻¹*scalarFieldStress g χ μ p*(g p)⁻¹) i=
      ((g p)⁻¹*scalarFieldStress g χ μ p*(g p)⁻¹) (sourceSymmetricPair i).1 (sourceSymmetricPair i).2:=by
    fin_cases i <;> rfl
  rw [hdecode,native_raise_source_matrix_identity _ _ hB]
  simp only [nativeRealClockVolume,coordinateVolumeDensity,abs_of_neg hn]

theorem native_scalar_clock_actual_source_represents_hilbert_density (g : MetricField)
    (hs : MetricFieldSymmetric g) (χ : CoordinatePoint → ℝ) (μ : ℝ)
    (hg : Continuous g) (hχ : ContDiff ℝ 2 χ) (hn : ∀ p∈Ω,(g p).det≠0)
    (frames : ∀ p∈Ω,∃ B:CoordinatePoint ≃L[ℝ] CoordinatePoint,LorentzFrameAt g p B)
    (i : Fin 10) (ψ : ScalarSourceProbe Ω) :
    representedMetricSource (nativeScalarClockMetricLF g χ μ hg hχ hn) i ψ=
      ∫ p,sourceDensityCoordinates (raisedSourceTensorDensity g (scalarFieldStress g χ μ)) i p*ψ p := by
  rw [nativeScalarClockMetricLF,native_clock_constructed_source_integral_components]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  by_cases hp:p∈Ω
  · obtain ⟨B,hB⟩:=frames p hp
    change nativeClockSourceCoefficient g (nativeScalarClockGradient χ) χ μ i p*ψ p=
      sourceDensityCoordinates (raisedSourceTensorDensity g (scalarFieldStress g χ μ)) i p*ψ p
    rw [native_clock_coefficient_is_actual_raised_density g hs χ μ p B hB]
  · have hz:ψ p=0:=by
      apply image_eq_zero_of_notMem_tsupport
      exact fun ht=>hp (ψ.tsupport_subset ht)
    simp [hz]

#print axioms native_component_functionals_reconstructed
#print axioms native_clock_constructed_source_integral_components
#print axioms native_lorentz_frame_determinant_negative
#print axioms native_raise_source_matrix_identity
#print axioms native_clock_coefficient_is_actual_raised_density
#print axioms native_scalar_clock_actual_source_represents_hilbert_density
end
end AASCSemanticExhaustion
