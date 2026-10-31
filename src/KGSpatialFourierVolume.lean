import KGSpatialSineFamily
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
namespace AASCKleinGordon

/-- The original sup-norm coordinate carrier and the Euclidean spatial carrier have
the same coordinate Lebesgue measure. The norms themselves are not identified. -/
theorem momentumEuclidean_preserves_volume : MeasurePreserving momentumEuclidean := by
  exact PiLp.volume_preserving_toLp (Fin 3)

theorem momentumEuclidean_symm_preserves_volume : MeasurePreserving momentumEuclidean.symm := by
  exact PiLp.volume_preserving_ofLp (Fin 3)

theorem momentumEuclidean_integral_change (f : KGSpatialSpace → ℂ) :
    (∫ p : Momentum, f (momentumEuclidean p))=∫ ξ : KGSpatialSpace, f ξ :=
  momentumEuclidean_preserves_volume.integral_comp momentumEuclidean.toHomeomorph.measurableEmbedding f

theorem momentumEuclidean_symm_integral_change (f : Momentum → ℂ) :
    (∫ ξ : KGSpatialSpace, f (momentumEuclidean.symm ξ))=∫ p : Momentum, f p :=
  momentumEuclidean_symm_preserves_volume.integral_comp momentumEuclidean.symm.toHomeomorph.measurableEmbedding f

/-- Exact cubic Jacobian for the original momentum p=2πℏ ξ. -/
theorem spatialSpectralMomentum_integral_change (a : Parameters) (f : Momentum → ℂ) :
    (∫ p : Momentum, f p)=(2*Real.pi*a.hbar)^3 •
      ∫ ξ : KGSpatialSpace, f (spatialSpectralMomentumCLM a ξ) := by
  let L := 2*Real.pi*a.hbar
  have hL : 0 < L := by have := a.hbar_pos; dsimp [L]; positivity
  have hh := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure KGSpatialSpace)
    (fun ξ => f (momentumEuclidean.symm (L • ξ))) hL.le
  have hh' : (∫ ξ : KGSpatialSpace, f (momentumEuclidean.symm ξ))=
      L^3 • ∫ ξ : KGSpatialSpace, f (momentumEuclidean.symm (L • ξ)) := by
    simpa only [smul_smul,mul_inv_cancel₀ (ne_of_gt hL),one_smul,
      finrank_euclideanSpace,Fintype.card_fin] using hh
  simpa only [spatialSpectralMomentumCLM,ContinuousLinearMap.smul_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.map_smul] using
    (momentumEuclidean_symm_integral_change f).symm.trans hh'

end AASCKleinGordon
