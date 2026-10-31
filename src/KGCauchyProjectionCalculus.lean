import KGConcreteCauchyTimeDynamics
import KGSpatialCauchyDifferential
import KGFlatFinitePropagation

noncomputable section
set_option maxHeartbeats 1200000
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

theorem kgSpatialLaplacian_spatialSineSolution (a : Parameters) (t : ℝ) (f : 𝓢(KGSpatialSpace,ℂ)) :
    kgSpatialLaplacian (spatialSineSolutionCLM a t f)=spatialSineSolutionCLM a t (kgSpatialLaplacian f) := by
  simp only [kgSpatialLaplacian,map_sum,kgSpatialPartial_spatialSineSolution]

theorem spatialAcceleration_eq_KG_PDE (a : Parameters) (t : ℝ) (f : 𝓢(KGSpatialSpace,ℂ)) :
    spatialAccelerationSolutionCLM a t f=kgSpatialLaplacian (spatialSineSolutionCLM a t f)-
      ((massWaveNumber a)^2 : ℂ) • spatialSineSolutionCLM a t f := by
  rw [spatialAcceleration_eq_neg_sine_operator,kgSpatialOperator,map_add,map_neg,map_smul,
    ← kgSpatialLaplacian_spatialSineSolution]
  module

theorem realProjection_complex_smul (P : ℂ →L[ℝ] ℝ) (r : ℝ) (z : ℂ) :
    P ((r : ℂ) • z)=r*P z := by
  simpa only [RCLike.real_smul_eq_coe_mul,smul_eq_mul] using P.map_smul r z

theorem projectedSchwartz_differentiable (P : ℂ →L[ℝ] ℝ) (f : 𝓢(KGSpatialSpace,ℂ)) :
    Differentiable ℝ (fun x => P (f x)) := P.differentiable.comp f.differentiable

theorem projectedSchwartz_partial (P : ℂ →L[ℝ] ℝ) (f : 𝓢(KGSpatialSpace,ℂ))
    (x : KGSpatialSpace) (i : Fin 3) :
    fderiv ℝ (fun y => P (f y)) x (kgSpatialDirection i)=P (kgSpatialPartialCLM i f x) := by
  change fderiv ℝ (P ∘ f) x (kgSpatialDirection i)=_
  rw [(P.hasFDerivAt.comp x f.differentiableAt.hasFDerivAt).fderiv]
  rfl

def projectedSinePosition (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ)
    (t : ℝ) (x : KGSpatialSpace) : ℝ := P (spatialSineSolutionCLM a t f x)

def projectedSineVelocity (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ)
    (t : ℝ) (x : KGSpatialSpace) : ℝ := P (spatialCosineSolutionCLM a t f x)

def projectedSineGradient (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ)
    (t : ℝ) (x : KGSpatialSpace) : KGSpatialSpace :=
  momentumEuclidean (fun i => P (spatialSineSolutionCLM a t (kgSpatialPartialCLM i f) x))

def projectedVelocityGradient (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ)
    (t : ℝ) (x : KGSpatialSpace) : KGSpatialSpace :=
  momentumEuclidean (fun i => P (spatialCosineSolutionCLM a t (kgSpatialPartialCLM i f) x))

theorem projectedSineGradient_apply (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ)
    (t : ℝ) (x : KGSpatialSpace) (i : Fin 3) :
    projectedSineGradient a f P t x i=P (spatialSineSolutionCLM a t (kgSpatialPartialCLM i f) x) := rfl

theorem projectedVelocityGradient_apply (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ)
    (t : ℝ) (x : KGSpatialSpace) (i : Fin 3) :
    projectedVelocityGradient a f P t x i=P (spatialCosineSolutionCLM a t (kgSpatialPartialCLM i f) x) := rfl

theorem projectedSinePosition_partial (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ)
    (t : ℝ) (x : KGSpatialSpace) (i : Fin 3) :
    fderiv ℝ (projectedSinePosition a f P t) x (kgSpatialDirection i)=projectedSineGradient a f P t x i := by
  unfold projectedSinePosition
  rw [projectedSchwartz_partial]
  rw [kgSpatialPartial_spatialSineSolution]
  rfl

theorem projectedSineVelocity_partial (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ)
    (t : ℝ) (x : KGSpatialSpace) (i : Fin 3) :
    fderiv ℝ (projectedSineVelocity a f P t) x (kgSpatialDirection i)=projectedVelocityGradient a f P t x i := by
  unfold projectedSineVelocity
  rw [projectedSchwartz_partial]
  rw [kgSpatialPartial_spatialCosineSolution]
  rfl

theorem projectedSineGradient_partial (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ)
    (t : ℝ) (x : KGSpatialSpace) (i j : Fin 3) :
    fderiv ℝ (fun y => projectedSineGradient a f P t y j) x (kgSpatialDirection i)=
      P (spatialSineSolutionCLM a t (kgSpatialPartialCLM i (kgSpatialPartialCLM j f)) x) := by
  simp only [projectedSineGradient_apply]
  rw [projectedSchwartz_partial,kgSpatialPartial_spatialSineSolution]

theorem projectedSineGradient_divergence (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ)
    (t : ℝ) (x : KGSpatialSpace) :
    kgSpatialDivergence (projectedSineGradient a f P t) x=P (kgSpatialLaplacian (spatialSineSolutionCLM a t f) x) := by
  rw [kgSpatialLaplacian_spatialSineSolution]
  simp only [kgSpatialDivergence,projectedSineGradient_partial,
    kgSpatialLaplacian,map_sum,SchwartzMap.sum_apply]

theorem projectedSinePosition_joint_continuous (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ) :
    Continuous (Function.uncurry (projectedSinePosition a f P)) :=
  P.continuous.comp (spatialSineSolution_joint_continuous a f)

theorem projectedSineVelocity_joint_continuous (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ) :
    Continuous (Function.uncurry (projectedSineVelocity a f P)) :=
  P.continuous.comp (spatialCosineSolution_joint_continuous a f)

theorem projectedSineGradient_joint_continuous (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ) :
    Continuous (Function.uncurry (projectedSineGradient a f P)) :=
  momentumEuclidean.continuous.comp (continuous_pi fun i =>
    P.continuous.comp (spatialSineSolution_joint_continuous a (kgSpatialPartialCLM i f)))

theorem projectedVelocityGradient_joint_continuous (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ) :
    Continuous (Function.uncurry (projectedVelocityGradient a f P)) :=
  momentumEuclidean.continuous.comp (continuous_pi fun i =>
    P.continuous.comp (spatialCosineSolution_joint_continuous a (kgSpatialPartialCLM i f)))

end AASCKleinGordon
