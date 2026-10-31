import KGSpacetimeEuclideanSplit
import KGSpatialCauchyDifferential

noncomputable section
set_option maxHeartbeats 1200000
open scoped SchwartzMap
namespace AASCKleinGordon

def spatialEuclideanInjection : KGSpatialSpace →L[ℝ] Spacetime :=
  spatialInjection.comp momentumEuclidean.symm.toContinuousLinearMap

def spacetimeSpatialSliceMap (t : ℝ) (x : KGSpatialSpace) : Spacetime := spacetimeSpatialJoin (t,x)

theorem spacetimeSpatialSliceMap_eq (t : ℝ) (x : KGSpatialSpace) :
    spacetimeSpatialSliceMap t x=timeInjection t+spatialEuclideanInjection x := by
  change fourCoordinateJoin (t,momentumEuclidean.symm x)=fourCoordinateJoin (t,0)+fourCoordinateJoin (0,momentumEuclidean.symm x)
  rw [← map_add]
  simp

theorem spacetimeSpatialSliceMap_temperate (t : ℝ) : (spacetimeSpatialSliceMap t).HasTemperateGrowth := by
  have he : spacetimeSpatialSliceMap t=(fun x => timeInjection t+spatialEuclideanInjection x) :=
    funext (spacetimeSpatialSliceMap_eq t)
  rw [he]
  exact (Function.HasTemperateGrowth.const (timeInjection t)).add spatialEuclideanInjection.hasTemperateGrowth

def spacetimeSpatialSliceCLM (t : ℝ) : 𝓢(Spacetime,ℂ) →L[ℂ] 𝓢(KGSpatialSpace,ℂ) :=
  SchwartzMap.compCLM ℂ (spacetimeSpatialSliceMap_temperate t) (by
    refine ⟨1,1,fun x => ?_⟩
    change ‖x‖ ≤ 1*(1+‖spacetimeSpatialJoin (t,x)‖)^1
    simpa only [pow_one,one_mul] using (norm_spatial_le_join t x).trans (by linarith))

theorem spacetimeSpatialSlice_apply (t : ℝ) (h : 𝓢(Spacetime,ℂ)) (x : KGSpatialSpace) :
    spacetimeSpatialSliceCLM t h x=h (spacetimeSpatialJoin (t,x)) := rfl

theorem spacetimeSpatialSliceMap_hasFDerivAt (t : ℝ) (x : KGSpatialSpace) :
    HasFDerivAt (spacetimeSpatialSliceMap t) spatialEuclideanInjection x := by
  have he : spacetimeSpatialSliceMap t=(fun x => timeInjection t+spatialEuclideanInjection x) :=
    funext (spacetimeSpatialSliceMap_eq t)
  rw [he]
  exact spatialEuclideanInjection.hasFDerivAt.const_add (timeInjection t)

theorem spatialEuclideanInjection_direction (i : Fin 3) :
    spatialEuclideanInjection (kgSpatialDirection i)=spacetimeCoordinateVector i.succ := by
  ext j
  cases j using Fin.cases with
  | zero => rfl
  | succ j =>
    change EuclideanSpace.single i (1 : ℝ) j=EuclideanSpace.single i.succ (1 : ℝ) j.succ
    simp [EuclideanSpace.single_apply]

theorem kgSpatialPartial_spacetimeSpatialSlice
    (t : ℝ) (h : 𝓢(Spacetime,ℂ)) (i : Fin 3) :
    kgSpatialPartialCLM i (spacetimeSpatialSliceCLM t h)=spacetimeSpatialSliceCLM t (spacetimePartialCLM i.succ h) := by
  ext x
  rw [kgSpatialPartial_apply,spacetimeSpatialSlice_apply]
  change fderiv ℝ (h ∘ spacetimeSpatialSliceMap t) x (kgSpatialDirection i)=_
  rw [(h.differentiableAt.hasFDerivAt.comp x (spacetimeSpatialSliceMap_hasFDerivAt t x)).fderiv]
  change fderiv ℝ h (spacetimeSpatialSliceMap t x) (spatialEuclideanInjection (kgSpatialDirection i))=_
  rw [spatialEuclideanInjection_direction]
  rfl

end AASCKleinGordon
