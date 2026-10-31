import KGConcreteSineSecondDerivatives

/-! The full sine-plus-cosine Fourier solution for arbitrary Schwartz pairs.
This assembles actual equations and traces; joint C-infinity, LF compact-data
continuity and local-domain uniqueness require their subsequent proofs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon.CurvedKG

def fullFlatPosition (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ))
    (t : ℝ) : 𝓢(KGSpatialSpace, ℂ) := spatialCosineSolutionCLM a t f + spatialSineSolutionCLM a t h

def fullFlatVelocity (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ))
    (t : ℝ) : 𝓢(KGSpatialSpace, ℂ) :=
  -spatialSineSolutionCLM a t (kgSpatialOperator a f) + spatialCosineSolutionCLM a t h

def fullFlatAcceleration (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ))
    (t : ℝ) : 𝓢(KGSpatialSpace, ℂ) :=
  -spatialCosineSolutionCLM a t (kgSpatialOperator a f) -
    spatialSineSolutionCLM a t (kgSpatialOperator a h)

def fullFlatPositionCLM (a : Parameters) (t : ℝ) :
    (𝓢(KGSpatialSpace, ℂ) × 𝓢(KGSpatialSpace, ℂ)) →L[ℂ] 𝓢(KGSpatialSpace, ℂ) :=
  (spatialCosineSolutionCLM a t).comp (ContinuousLinearMap.fst ℂ _ _) +
    (spatialSineSolutionCLM a t).comp (ContinuousLinearMap.snd ℂ _ _)

theorem full_flat_position_clm_apply (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ)) (t : ℝ) :
    fullFlatPositionCLM a t (f, h) = fullFlatPosition a f h t := rfl

theorem full_flat_initial_position (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ)) :
    fullFlatPosition a f h 0 = f := by
  simp [fullFlatPosition, spatialCosineSolution_zero, spatialSineSolution_zero]

theorem full_flat_initial_velocity (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ)) :
    fullFlatVelocity a f h 0 = h := by
  simp [fullFlatVelocity, spatialCosineSolution_zero, spatialSineSolution_zero]

theorem full_flat_position_hasDerivAt (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ))
    (t : ℝ) (x : KGSpatialSpace) :
    HasDerivAt (fun s => fullFlatPosition a f h s x) (fullFlatVelocity a f h t x) t := by
  have result := (spatialCosineSolution_hasDerivAt a f t x).add
    (spatialSineSolution_hasDerivAt a h t x)
  simpa only [fullFlatPosition, fullFlatVelocity, SchwartzMap.add_apply, SchwartzMap.neg_apply,
    spatialAcceleration_eq_neg_sine_operator] using result

theorem full_flat_velocity_hasDerivAt (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ))
    (t : ℝ) (x : KGSpatialSpace) :
    HasDerivAt (fun s => fullFlatVelocity a f h s x) (fullFlatAcceleration a f h t x) t := by
  have result := (spatialSineSolution_hasDerivAt a (kgSpatialOperator a f) t x).neg.add
    (spatialCosineSolution_hasDerivAt a h t x)
  simpa only [fullFlatVelocity, fullFlatAcceleration, SchwartzMap.add_apply, SchwartzMap.neg_apply,
    SchwartzMap.sub_apply, spatialAcceleration_eq_neg_sine_operator, sub_eq_add_neg] using result

theorem full_flat_position_joint_continuous (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ)) :
    Continuous (fun z : ℝ × KGSpatialSpace => fullFlatPosition a f h z.1 z.2) :=
  (spatialCosineSolution_joint_continuous a f).add (spatialSineSolution_joint_continuous a h)

theorem full_flat_velocity_joint_continuous (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ)) :
    Continuous (fun z : ℝ × KGSpatialSpace => fullFlatVelocity a f h z.1 z.2) :=
  (spatialSineSolution_joint_continuous a (kgSpatialOperator a f)).neg.add
    (spatialCosineSolution_joint_continuous a h)

theorem full_flat_acceleration_joint_continuous (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ)) :
    Continuous (fun z : ℝ × KGSpatialSpace => fullFlatAcceleration a f h z.1 z.2) :=
  (spatialCosineSolution_joint_continuous a (kgSpatialOperator a f)).neg.sub
    (spatialSineSolution_joint_continuous a (kgSpatialOperator a h))

theorem laplacian_cosine_commutes (a : Parameters) (t : ℝ) (f : 𝓢(KGSpatialSpace, ℂ)) :
    kgSpatialLaplacian (spatialCosineSolutionCLM a t f) =
      spatialCosineSolutionCLM a t (kgSpatialLaplacian f) := by
  simp only [kgSpatialLaplacian, map_sum, kgSpatialPartial_spatialCosineSolution]

theorem full_flat_acceleration_equation (a : Parameters) (t : ℝ) (f h : 𝓢(KGSpatialSpace, ℂ)) :
    fullFlatAcceleration a f h t = kgSpatialLaplacian (fullFlatPosition a f h t) -
      ((massWaveNumber a) ^ 2 : ℂ) • fullFlatPosition a f h t := by
  simp only [fullFlatAcceleration, fullFlatPosition, kgSpatialOperator, map_add, map_neg, map_smul,
    ← laplacian_cosine_commutes, ← kgSpatialLaplacian_spatialSineSolution]
  simp only [kgSpatialLaplacian, map_add, Finset.sum_add_distrib]
  module

theorem full_flat_position_spatial_partial (a : Parameters) (t : ℝ)
    (f h : 𝓢(KGSpatialSpace, ℂ)) (i : Fin 3) :
    kgSpatialPartialCLM i (fullFlatPosition a f h t) =
      fullFlatPosition a (kgSpatialPartialCLM i f) (kgSpatialPartialCLM i h) t := by
  simp only [fullFlatPosition, map_add, kgSpatialPartial_spatialCosineSolution,
    kgSpatialPartial_spatialSineSolution]

theorem full_flat_projected_initial_position (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ))
    (P : ℂ →L[ℝ] ℝ) (x : KGSpatialSpace) : P (fullFlatPosition a f h 0 x) = P (f x) := by
  rw [full_flat_initial_position]

theorem full_flat_projected_initial_velocity (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ))
    (P : ℂ →L[ℝ] ℝ) (x : KGSpatialSpace) :
    HasDerivAt (fun s => P (fullFlatPosition a f h s x)) (P (h x)) 0 := by
  have first := P.hasFDerivAt.comp_hasDerivAt 0 (full_flat_position_hasDerivAt a f h 0 x)
  simpa only [full_flat_initial_velocity] using first

end AASCKleinGordon.CurvedKG
