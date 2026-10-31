import WickKGOriginalActionProtocols
import KGOriginalWickActionReality

noncomputable section
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem wick_original_finite_action_hermitian (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) :
    star (wickOriginalFiniteAction a s u v H)=wickOriginalFiniteAction a s v u H := by
  have huv : wickOriginalFiniteAction a s u v H=
      originalWickScalarRelativeAction a s u v (wickNativeMetricVariation H) 1 := by
    simpa only [one_smul] using wick_original_finite_action_on_direction a s u v H 1
  have hvu : wickOriginalFiniteAction a s v u H=
      originalWickScalarRelativeAction a s v u (wickNativeMetricVariation H) 1 := by
    simpa only [one_smul] using wick_original_finite_action_on_direction a s v u H 1
  rw [huv,hvu]
  exact original_wick_relative_action_hermitian a s u v _ 1

theorem wick_original_finite_action_diagonal_real (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) :
    (wickOriginalFiniteAction a s u u H).im=0 := by
  have h := congrArg Complex.im (wick_original_finite_action_hermitian a s u u H)
  simp only [Complex.star_def,Complex.conj_im] at h
  linarith

theorem wick_KG_finite_carrier_is_actual_real_action (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) (H : WickKGAdmittedFiniteMetric Ω) :
    (wickKGFiniteActionCarrier a s u Ω H : ℂ)=wickOriginalFiniteAction a s u u H.val := by
  apply Complex.ext
  · rfl
  · change 0=(wickOriginalFiniteAction a s u u H.val).im
    exact (wick_original_finite_action_diagonal_real a s u H.val).symm

end AASCKleinGordon
