import KGNativeWickTensorDensity
import WickNativeWardConservation

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickOriginalNativeRealTensor (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    (p : CoordinatePoint) (i j : Fin 4) : ℝ := (originalWickNativeStressDensity a s u u p i j).re

theorem wick_original_native_real_tensor_smooth (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (i j : Fin 4) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => wickOriginalNativeRealTensor a s u p i j) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (originalWickScalarStressRaisedMatrix a s u u i j) :=
    contDiff_const.mul (originalWickScalarStressCandidateMatrix_smooth a s u u i j)
  exact Complex.reCLM.contDiff.comp (h.comp wickSpacetimeCoordinates.symm.contDiff)

theorem wick_original_native_tensor_is_real (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (p : CoordinatePoint) (i j : Fin 4) :
    originalWickNativeStressDensity a s u u p i j=(wickOriginalNativeRealTensor a s u p i j : ℂ) := by
  apply Complex.ext
  · rfl
  · exact original_wick_scalar_stress_diagonal_real a s u i j (wickSpacetimeCoordinates.symm p)

theorem wick_original_native_real_tensor_symmetric (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (p : CoordinatePoint) (i j : Fin 4) :
    wickOriginalNativeRealTensor a s u p i j=wickOriginalNativeRealTensor a s u p j i := by
  unfold wickOriginalNativeRealTensor originalWickNativeStressDensity originalWickScalarStressRaisedMatrix
  rw [originalWickScalarStressCandidateMatrix_symmetric a s u u i j]
  congr 1
  ring

theorem wick_original_native_real_tensor_represents (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω) :
    originalWickNativeRealMetricResponse a s u Ω H=
      (1/2 : ℝ)*∫ p,∑ i,∑ j,tensorEncode (H p) i j*wickOriginalNativeRealTensor a s u p i j :=
  original_wick_native_real_response_tensor_density a s u Ω H

/-- The fixed realization has the whole boundaryless coordinate spacetime as
its closed support envelope. This asserts no compact support of the state. -/
def wickOriginalClosedSupportEnvelope : Set CoordinatePoint := Set.univ

theorem wick_original_support_envelope_closed : IsClosed wickOriginalClosedSupportEnvelope := isClosed_univ
theorem wick_original_support_envelope_boundary_empty :
    frontier wickOriginalClosedSupportEnvelope=∅ := frontier_univ

theorem wick_original_native_tensor_supported (a : Parameters) (s : ℝ) (u : FiniteParticleCore) :
    Function.support (wickOriginalNativeRealTensor a s u)⊆wickOriginalClosedSupportEnvelope :=
  Set.subset_univ _

theorem wick_original_native_real_tensor_vacuum (a : Parameters) (s : ℝ)
    (p : CoordinatePoint) (i j : Fin 4) : wickOriginalNativeRealTensor a s vacuumCore p i j=0 := by
  simp only [wickOriginalNativeRealTensor,originalWickNativeStressDensity,
    originalWickScalarStressRaisedMatrix,originalWickScalarStressCandidateMatrix_vacuum,
    mul_zero,Complex.zero_re]

/-- Concrete witness ledger. Regularity, reality, support and closed Ward
conditions are proved fields, not arbitrary proposition labels. -/
structure WickNativeOriginalTensorLedger (a : Parameters) (s : ℝ) (u : FiniteParticleCore) where
  density : CoordinatePoint → Fin 4 → Fin 4 → ℝ
  same_tensor : density=wickOriginalNativeRealTensor a s u
  smooth : ∀ i j,ContDiff ℝ (⊤ : ℕ∞) (fun p => density p i j)
  symmetric : ∀ p i j,density p i j=density p j i
  complex_evaluation : ∀ p i j,originalWickNativeStressDensity a s u u p i j=(density p i j : ℂ)
  represents : ∀ (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω),
    originalWickNativeRealMetricResponse a s u Ω H=
      (1/2 : ℝ)*∫ p,∑ i,∑ j,tensorEncode (H p) i j*density p i j
  supported : Function.support density⊆wickOriginalClosedSupportEnvelope
  envelope_closed : IsClosed wickOriginalClosedSupportEnvelope
  boundary_empty : frontier wickOriginalClosedSupportEnvelope=∅
  closed_ward : ∀ (Ω : Opens CoordinatePoint) (X : CoordinateVectorProbe Ω),
    originalWickNativeRealMetricResponse a s u Ω
      (compactMetricLieCLM Ω wickNativeFlatMetric wick_native_flat_smooth X)=0
  divergence_zero : ∀ Ω,constructedSourceDivergence Ω wickNativeFlatMetric wick_native_flat_smooth
    (originalWickNativeRepresentedSource a s u Ω)=0

def wickNativeOriginalTensorLedger (a : Parameters) (s : ℝ) (u : FiniteParticleCore) :
    WickNativeOriginalTensorLedger a s u where
  density := wickOriginalNativeRealTensor a s u
  same_tensor := rfl
  smooth := wick_original_native_real_tensor_smooth a s u
  symmetric := wick_original_native_real_tensor_symmetric a s u
  complex_evaluation := wick_original_native_tensor_is_real a s u
  represents := wick_original_native_real_tensor_represents a s u
  supported := wick_original_native_tensor_supported a s u
  envelope_closed := wick_original_support_envelope_closed
  boundary_empty := wick_original_support_envelope_boundary_empty
  closed_ward := original_wick_native_real_lie_ward a s u
  divergence_zero := original_wick_native_represented_source_divergence_zero a s u

end AASCKleinGordon
