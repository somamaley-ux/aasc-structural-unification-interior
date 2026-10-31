import KGConcreteSineFinitePropagation
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
set_option maxHeartbeats 1400000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem spatialSineSolution_initial_spatial_partial
    (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (x : KGSpatialSpace) (i : Fin 3) :
    fderiv ℝ (spatialSineSolutionCLM a 0 f) x (kgSpatialDirection i)=0 := by
  rw [← kgSpatialPartial_apply,kgSpatialPartial_spatialSineSolution,spatialSineSolution_zero]
  rfl

theorem spatialSineSolution_nonzero_for_nonzero_data
    (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (hf : f ≠ 0) :
    ∃ t : ℝ, spatialSineSolutionCLM a t f ≠ 0 := by
  by_contra hn
  have hz : ∀ t : ℝ, spatialSineSolutionCLM a t f=0 := by simpa only [not_exists,not_not] using hn
  have hfzero : f=0 := by
    ext x
    have hd := spatialSineSolution_initial_velocity a f x
    have he : (fun t => spatialSineSolutionCLM a t f x)=(fun _ : ℝ => (0 : ℂ)) := by
      funext t
      rw [hz t]
      rfl
    rw [he] at hd
    exact hd.unique (hasDerivAt_const 0 0)
  exact hf hfzero

theorem spatialSineSolution_second_time_hasDerivAt
    (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (t : ℝ) (x : KGSpatialSpace) :
    HasDerivAt (fun s => deriv (fun r => spatialSineSolutionCLM a r f x) s)
      (-spatialSineSolutionCLM a t (kgSpatialOperator a f) x) t := by
  have he : (fun s => deriv (fun r => spatialSineSolutionCLM a r f x) s)=
      (fun s => spatialCosineSolutionCLM a s f x) :=
    funext (fun s => (spatialSineSolution_hasDerivAt a f s x).deriv)
  rw [he]
  simpa only [spatialAcceleration_eq_neg_sine_operator,SchwartzMap.neg_apply]
    using spatialCosineSolution_hasDerivAt a f t x

theorem spatialSineSolution_time_contDiff_two
    (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (x : KGSpatialSpace) :
    ContDiff ℝ 2 (fun t => spatialSineSolutionCLM a t f x) := by
  have h1 : deriv (fun r => spatialSineSolutionCLM a r f x)=
      (fun s => spatialCosineSolutionCLM a s f x) :=
    funext (fun s => (spatialSineSolution_hasDerivAt a f s x).deriv)
  have h2 : deriv (fun r => spatialCosineSolutionCLM a r f x)=
      (fun s => -spatialSineSolutionCLM a s (kgSpatialOperator a f) x) := by
    funext s
    simpa only [spatialAcceleration_eq_neg_sine_operator,SchwartzMap.neg_apply]
      using (spatialCosineSolution_hasDerivAt a f s x).deriv
  rw [show (2 : WithTop ℕ∞)=1+1 from rfl,contDiff_succ_iff_deriv]
  refine ⟨fun s => (spatialSineSolution_hasDerivAt a f s x).differentiableAt,by simp,?_⟩
  rw [h1,contDiff_one_iff_deriv]
  refine ⟨fun s => (spatialCosineSolution_hasDerivAt a f s x).differentiableAt,?_⟩
  rw [h2]
  exact ((spatialSineSolution_joint_continuous a (kgSpatialOperator a f)).comp
    (continuous_id.prodMk continuous_const)).neg

theorem spatialSineSolution_second_time_joint_continuous
    (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) :
    Continuous (fun z : ℝ × KGSpatialSpace =>
      deriv (fun s => deriv (fun r => spatialSineSolutionCLM a r f z.2) s) z.1) := by
  have he (t : ℝ) (x : KGSpatialSpace) := (spatialSineSolution_second_time_hasDerivAt a f t x).deriv
  simp_rw [he]
  exact (spatialSineSolution_joint_continuous a (kgSpatialOperator a f)).neg

theorem spatialSineSolution_spatial_partial_joint_continuous
    (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (i : Fin 3) :
    Continuous (fun z : ℝ × KGSpatialSpace =>
      fderiv ℝ (spatialSineSolutionCLM a z.1 f) z.2 (kgSpatialDirection i)) := by
  simp_rw [← kgSpatialPartial_apply,kgSpatialPartial_spatialSineSolution]
  exact spatialSineSolution_joint_continuous a (kgSpatialPartialCLM i f)

theorem spatialSineSolution_spatial_second_partial
    (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (t : ℝ) (x : KGSpatialSpace) (i j : Fin 3) :
    fderiv ℝ (fun y => fderiv ℝ (spatialSineSolutionCLM a t f) y (kgSpatialDirection i))
      x (kgSpatialDirection j)=spatialSineSolutionCLM a t (kgSpatialPartialCLM j (kgSpatialPartialCLM i f)) x := by
  change kgSpatialPartialCLM j (kgSpatialPartialCLM i (spatialSineSolutionCLM a t f)) x=_
  rw [kgSpatialPartial_spatialSineSolution,kgSpatialPartial_spatialSineSolution]

theorem spatialSineSolution_spatial_second_joint_continuous
    (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (i j : Fin 3) :
    Continuous (fun z : ℝ × KGSpatialSpace =>
      fderiv ℝ (fun y => fderiv ℝ (spatialSineSolutionCLM a z.1 f) y (kgSpatialDirection i))
        z.2 (kgSpatialDirection j)) := by
  simp_rw [spatialSineSolution_spatial_second_partial]
  exact spatialSineSolution_joint_continuous a (kgSpatialPartialCLM j (kgSpatialPartialCLM i f))

theorem spatialSineSolution_mixed_hasDerivAt
    (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (t : ℝ) (x : KGSpatialSpace) (i : Fin 3) :
    HasDerivAt (fun s => fderiv ℝ (spatialSineSolutionCLM a s f) x (kgSpatialDirection i))
      (spatialCosineSolutionCLM a t (kgSpatialPartialCLM i f) x) t := by
  simp_rw [← kgSpatialPartial_apply,kgSpatialPartial_spatialSineSolution]
  exact spatialSineSolution_hasDerivAt a (kgSpatialPartialCLM i f) t x

theorem spatialSineSolution_mixed_joint_continuous
    (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (i : Fin 3) :
    Continuous (fun z : ℝ × KGSpatialSpace =>
      deriv (fun s => fderiv ℝ (spatialSineSolutionCLM a s f) z.2 (kgSpatialDirection i)) z.1) := by
  simp_rw [fun t x => (spatialSineSolution_mixed_hasDerivAt a f t x i).deriv]
  exact spatialCosineSolution_joint_continuous a (kgSpatialPartialCLM i f)

end AASCKleinGordon
