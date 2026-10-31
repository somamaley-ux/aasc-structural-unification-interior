import KGSpatialFourierVolume
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
namespace AASCKleinGordon

def spacetimeSpatialJoin : (ℝ × KGSpatialSpace) ≃L[ℝ] Spacetime :=
  ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr momentumEuclidean.symm).trans fourCoordinateJoin

theorem spacetimeSpatialJoin_zero (t : ℝ) (x : KGSpatialSpace) : spacetimeSpatialJoin (t,x) 0=t := rfl

theorem spacetimeSpatialJoin_succ (t : ℝ) (x : KGSpatialSpace) (i : Fin 3) :
    spacetimeSpatialJoin (t,x) i.succ=x i := rfl

theorem spacetimeSpatialJoin_norm_sq (t : ℝ) (x : KGSpatialSpace) :
    ‖spacetimeSpatialJoin (t,x)‖^2=t^2+‖x‖^2 := by
  rw [EuclideanSpace.norm_sq_eq,Fin.sum_univ_succ,EuclideanSpace.norm_sq_eq]
  simp only [spacetimeSpatialJoin_zero,spacetimeSpatialJoin_succ,Real.norm_eq_abs,sq_abs]

theorem norm_spatial_le_join (t : ℝ) (x : KGSpatialSpace) :
    ‖x‖ ≤ ‖spacetimeSpatialJoin (t,x)‖ := by
  nlinarith [spacetimeSpatialJoin_norm_sq t x,sq_nonneg t,norm_nonneg x,norm_nonneg (spacetimeSpatialJoin (t,x))]

theorem fourCoordinateCons_preserves_volume : MeasurePreserving fourCoordinateCons := by
  have hh := (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) (0 : Fin 4)).symm
  convert hh using 1
  ext z i
  simp only [fourCoordinateCons,LinearEquiv.coe_toContinuousLinearEquiv,LinearEquiv.coe_mk,
    MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Fin.insertNth_zero,
    Equiv.coe_fn_mk,Fin.zero_succAbove]
  rfl

theorem fourCoordinateJoin_preserves_volume : MeasurePreserving fourCoordinateJoin :=
  (PiLp.volume_preserving_toLp (Fin 4)).comp fourCoordinateCons_preserves_volume

theorem spacetimeSpatialJoin_preserves_volume : MeasurePreserving spacetimeSpatialJoin := by
  apply fourCoordinateJoin_preserves_volume.comp
  exact (MeasurePreserving.id (volume : Measure ℝ)).prod momentumEuclidean_symm_preserves_volume

/-- The exact tau=x0 spatial split of the original spacetime Lebesgue measure. -/
theorem spacetimeSpatialJoin_integral (g : Spacetime → ℂ) :
    (∫ z : Spacetime, g z)=∫ z : ℝ × KGSpatialSpace, g (spacetimeSpatialJoin z) :=
  (spacetimeSpatialJoin_preserves_volume.integral_comp spacetimeSpatialJoin.toHomeomorph.measurableEmbedding g).symm

end AASCKleinGordon
