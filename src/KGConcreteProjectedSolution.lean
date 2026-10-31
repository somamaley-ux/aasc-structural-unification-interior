import KGCauchyProjectionCalculus

noncomputable section
set_option maxHeartbeats 1400000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem projectedSinePosition_hasDerivAt (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ)
    (t : ℝ) (x : KGSpatialSpace) :
    HasDerivAt (fun s => projectedSinePosition a f P s x) (projectedSineVelocity a f P t x) t :=
  P.hasFDerivAt.comp_hasDerivAt t (spatialSineSolution_hasDerivAt a f t x)

theorem projectedSineVelocity_hasDerivAt (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ)
    (t : ℝ) (x : KGSpatialSpace) :
    HasDerivAt (fun s => projectedSineVelocity a f P s x)
      (kgSpatialDivergence (projectedSineGradient a f P t) x-
        (massWaveNumber a)^2*projectedSinePosition a f P t x) t := by
  have hd := P.hasFDerivAt.comp_hasDerivAt t (spatialCosineSolution_hasDerivAt a f t x)
  convert hd using 1
  rw [spatialAcceleration_eq_KG_PDE,SchwartzMap.sub_apply,P.map_sub]
  rw [projectedSineGradient_divergence]
  congr 1
  change (massWaveNumber a)^2*P (spatialSineSolutionCLM a t f x)=
    P ((massWaveNumber a : ℂ)^2 • spatialSineSolutionCLM a t f x)
  exact (realProjection_complex_smul P ((massWaveNumber a)^2) (spatialSineSolutionCLM a t f x)).symm.trans
    (congrArg (fun r : ℂ => P (r • spatialSineSolutionCLM a t f x)) (Complex.ofReal_pow (massWaveNumber a) 2))

theorem projectedSineGradient_hasDerivAt (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ)
    (t : ℝ) (x : KGSpatialSpace) :
    HasDerivAt (fun s => projectedSineGradient a f P s x) (projectedVelocityGradient a f P t x) t := by
  apply momentumEuclidean.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
  apply hasDerivAt_pi.mpr
  intro i
  exact P.hasFDerivAt.comp_hasDerivAt t (spatialSineSolution_hasDerivAt a (kgSpatialPartialCLM i f) t x)

theorem projectedSineFlux_spatial (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ)
    (t : ℝ) (i : Fin 3) :
    Differentiable ℝ (fun x => flatEnergyFlux (projectedSineVelocity a f P) (projectedSineGradient a f P) t x i) := by
  change Differentiable ℝ (fun x => P (spatialCosineSolutionCLM a t f x)*
    P (spatialSineSolutionCLM a t (kgSpatialPartialCLM i f) x))
  exact (projectedSchwartz_differentiable P _).mul (projectedSchwartz_differentiable P _)

theorem projectedSineFlux_partial (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ)
    (t : ℝ) (x : KGSpatialSpace) (i : Fin 3) :
    fderiv ℝ (fun y => flatEnergyFlux (projectedSineVelocity a f P) (projectedSineGradient a f P) t y i)
      x (kgSpatialDirection i)=
      projectedVelocityGradient a f P t x i*projectedSineGradient a f P t x i+
      projectedSineVelocity a f P t x*
        P (spatialSineSolutionCLM a t (kgSpatialPartialCLM i (kgSpatialPartialCLM i f)) x) := by
  let V := projectedSineVelocity a f P t
  let W := fun y => projectedSineGradient a f P t y i
  change fderiv ℝ (V*W) x (kgSpatialDirection i)=_
  have hv : Differentiable ℝ V := projectedSchwartz_differentiable P _
  have hw : Differentiable ℝ W := projectedSchwartz_differentiable P _
  rw [((hv x).hasFDerivAt.mul (hw x).hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  change V x*fderiv ℝ W x (kgSpatialDirection i)+W x*fderiv ℝ V x (kgSpatialDirection i)=_
  rw [projectedSineVelocity_partial,projectedSineGradient_partial]
  ring

theorem projectedSineFlux_partial_joint_continuous
    (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ) (i : Fin 3) :
    Continuous (fun z : ℝ × KGSpatialSpace =>
      fderiv ℝ (fun y => flatEnergyFlux (projectedSineVelocity a f P) (projectedSineGradient a f P) z.1 y i)
        z.2 (kgSpatialDirection i)) := by
  simp_rw [projectedSineFlux_partial,projectedVelocityGradient_apply,projectedSineGradient_apply]
  exact ((P.continuous.comp (spatialCosineSolution_joint_continuous a (kgSpatialPartialCLM i f))).mul
    (P.continuous.comp (spatialSineSolution_joint_continuous a (kgSpatialPartialCLM i f)))).add
    ((projectedSineVelocity_joint_continuous a f P).mul
      (P.continuous.comp (spatialSineSolution_joint_continuous a (kgSpatialPartialCLM i (kgSpatialPartialCLM i f)))))

theorem projectedSineFlux_partial_continuous
    (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ) (t : ℝ) (i : Fin 3) :
    Continuous (fun x : KGSpatialSpace =>
      fderiv ℝ (fun y => flatEnergyFlux (projectedSineVelocity a f P) (projectedSineGradient a f P) t y i)
        x (kgSpatialDirection i)) := by
  simp_rw [projectedSineFlux_partial,projectedVelocityGradient_apply,projectedSineGradient_apply,projectedSineVelocity]
  exact ((P.continuous.comp (spatialCosineSolutionCLM a t (kgSpatialPartialCLM i f)).continuous).mul
    (P.continuous.comp (spatialSineSolutionCLM a t (kgSpatialPartialCLM i f)).continuous)).add
    ((P.continuous.comp (spatialCosineSolutionCLM a t f).continuous).mul
      (P.continuous.comp (spatialSineSolutionCLM a t (kgSpatialPartialCLM i (kgSpatialPartialCLM i f))).continuous))

theorem projectedSineFlux_divergence_continuous
    (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ) :
    Continuous (fun z : ℝ × KGSpatialSpace =>
      kgSpatialDivergence (flatEnergyFlux (projectedSineVelocity a f P) (projectedSineGradient a f P) z.1) z.2) := by
  apply continuous_finset_sum
  intro i hi
  exact projectedSineFlux_partial_joint_continuous a f P i

/-- Every field of the analytic first-order KG record is discharged from the actual
Fourier sine family and its derivatives. In particular w is its actual spatial gradient. -/
def concreteProjectedSineSolution (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ) :
    FlatKGFirstOrderSolution (massWaveNumber a) where
  u := projectedSinePosition a f P
  v := projectedSineVelocity a f P
  w := projectedSineGradient a f P
  gradientV := projectedVelocityGradient a f P
  continuousU := projectedSinePosition_joint_continuous a f P
  continuousV := projectedSineVelocity_joint_continuous a f P
  continuousW := projectedSineGradient_joint_continuous a f P
  spatialV t := projectedSchwartz_differentiable P _
  spatialW t i := projectedSchwartz_differentiable P _
  gradientV_eq := projectedSineVelocity_partial a f P
  timeU := projectedSinePosition_hasDerivAt a f P
  timeV := projectedSineVelocity_hasDerivAt a f P
  timeW := projectedSineGradient_hasDerivAt a f P
  divergenceContinuous := projectedSineFlux_divergence_continuous a f P
  fluxSpatial := projectedSineFlux_spatial a f P
  fluxDerivativeContinuous := projectedSineFlux_partial_continuous a f P

theorem concreteProjectedSine_initial_position (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ)
    (x : KGSpatialSpace) : (concreteProjectedSineSolution a f P).u 0 x=0 := by
  change P (spatialSineSolutionCLM a 0 f x)=0
  rw [spatialSineSolution_zero]
  exact P.map_zero

theorem concreteProjectedSine_initial_velocity (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ)
    (x : KGSpatialSpace) : (concreteProjectedSineSolution a f P).v 0 x=P (f x) := by
  change P (spatialCosineSolutionCLM a 0 f x)=P (f x)
  rw [spatialCosineSolution_zero]

theorem concreteProjectedSine_initial_gradient (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (P : ℂ →L[ℝ] ℝ)
    (x : KGSpatialSpace) : (concreteProjectedSineSolution a f P).w 0 x=0 := by
  ext i
  change P (spatialSineSolutionCLM a 0 (kgSpatialPartialCLM i f) x)=0
  rw [spatialSineSolution_zero]
  exact P.map_zero

end AASCKleinGordon
