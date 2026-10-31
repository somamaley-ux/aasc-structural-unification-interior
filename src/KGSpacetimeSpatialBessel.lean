import KGSpacetimeSpatialSlices

noncomputable section
set_option maxHeartbeats 1400000
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

def spacetimeSpatialLaplacian (h : 𝓢(Spacetime,ℂ)) : 𝓢(Spacetime,ℂ) :=
  ∑ i : Fin 3, spacetimePartialCLM i.succ (spacetimePartialCLM i.succ h)

def spacetimeSpatialBessel (h : 𝓢(Spacetime,ℂ)) : 𝓢(Spacetime,ℂ) := h-spacetimeSpatialLaplacian h

def spatialBessel (f : 𝓢(KGSpatialSpace,ℂ)) : 𝓢(KGSpatialSpace,ℂ) := f-kgSpatialLaplacian f

def spatialBesselWeight (ξ : KGSpatialSpace) : ℝ := 1+(2*Real.pi)^2*‖ξ‖^2

theorem spatialBesselWeight_pos (ξ : KGSpatialSpace) : 0 < spatialBesselWeight ξ := by
  unfold spatialBesselWeight
  positivity

theorem kgSpatialLaplacian_spacetimeSpatialSlice (t : ℝ) (h : 𝓢(Spacetime,ℂ)) :
    kgSpatialLaplacian (spacetimeSpatialSliceCLM t h)=spacetimeSpatialSliceCLM t (spacetimeSpatialLaplacian h) := by
  simp only [kgSpatialLaplacian,spacetimeSpatialLaplacian,map_sum,kgSpatialPartial_spacetimeSpatialSlice]

theorem spatialBessel_spacetimeSpatialSlice (t : ℝ) (h : 𝓢(Spacetime,ℂ)) :
    spatialBessel (spacetimeSpatialSliceCLM t h)=spacetimeSpatialSliceCLM t (spacetimeSpatialBessel h) := by
  simp only [spatialBessel,spacetimeSpatialBessel,map_sub,kgSpatialLaplacian_spacetimeSpatialSlice]

theorem fourier_spatialBessel (f : 𝓢(KGSpatialSpace,ℂ)) (ξ : KGSpatialSpace) :
    𝓕 (spatialBessel f) ξ=(spatialBesselWeight ξ : ℂ)*𝓕 f ξ := by
  simp only [spatialBessel,sub_eq_add_neg,FourierTransform.fourier_add,FourierTransform.fourier_neg,
    SchwartzMap.add_apply,SchwartzMap.neg_apply,fourier_kgSpatialLaplacian,spatialBesselWeight]
  push_cast
  ring

theorem fourier_spacetimeSpatialBessel_twice_slice (t : ℝ) (h : 𝓢(Spacetime,ℂ)) (ξ : KGSpatialSpace) :
    𝓕 (spacetimeSpatialSliceCLM t (spacetimeSpatialBessel (spacetimeSpatialBessel h))) ξ=
      (spatialBesselWeight ξ : ℂ)^2*𝓕 (spacetimeSpatialSliceCLM t h) ξ := by
  rw [← spatialBessel_spacetimeSpatialSlice,← spatialBessel_spacetimeSpatialSlice,
    fourier_spatialBessel,fourier_spatialBessel]
  ring

theorem spacetimePartial_tsupport_subset (i : Fin 4) (h : 𝓢(Spacetime,ℂ)) :
    tsupport (spacetimePartialCLM i h : Spacetime → ℂ) ⊆ tsupport (h : Spacetime → ℂ) :=
  SchwartzMap.tsupport_lineDerivOp_subset (spacetimeCoordinateVector i) h

theorem spacetimeSpatialBessel_tsupport_subset (h : 𝓢(Spacetime,ℂ)) :
    tsupport (spacetimeSpatialBessel h : Spacetime → ℂ) ⊆ tsupport (h : Spacetime → ℂ) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro z hz
  by_contra hn
  have hzero : h z=0 := image_eq_zero_of_notMem_tsupport hn
  have hd (i : Fin 3) : spacetimePartialCLM i.succ (spacetimePartialCLM i.succ h) z=0 :=
    image_eq_zero_of_notMem_tsupport (fun hc => hn
      ((spacetimePartial_tsupport_subset i.succ h)
        ((spacetimePartial_tsupport_subset i.succ (spacetimePartialCLM i.succ h)) hc)))
  have hh : spacetimeSpatialBessel h z=0 := by
    simp only [spacetimeSpatialBessel,SchwartzMap.sub_apply,spacetimeSpatialLaplacian,
      SchwartzMap.sum_apply,hzero,hd,Finset.sum_const_zero,sub_zero]
  exact hz hh

theorem spacetimeSpatialBessel_twice_tsupport_subset (h : 𝓢(Spacetime,ℂ)) :
    tsupport (spacetimeSpatialBessel (spacetimeSpatialBessel h) : Spacetime → ℂ) ⊆ tsupport (h : Spacetime → ℂ) :=
  (spacetimeSpatialBessel_tsupport_subset (spacetimeSpatialBessel h)).trans (spacetimeSpatialBessel_tsupport_subset h)

end AASCKleinGordon
