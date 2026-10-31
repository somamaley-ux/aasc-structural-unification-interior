import SKGScalarHamiltonian

/-! Actual three-dimensional spatial derivatives and compact integration
by parts, for the spatial carrier already used by Stage1. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

def spatialPartial (F : KGSpatialSpace → ℝ) (x : KGSpatialSpace) (i : Fin 3) : ℝ :=
  fderiv ℝ F x (kgSpatialDirection i)

theorem spatial_partial_smooth (F : KGSpatialSpace → ℝ)
    (regular : ContDiff ℝ (⊤ : ℕ∞) F) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => spatialPartial F x i) :=
  (regular.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem spatial_partial_compact (F : KGSpatialSpace → ℝ) (compact : HasCompactSupport F)
    (i : Fin 3) : HasCompactSupport (fun x => spatialPartial F x i) :=
  (compact.fderiv ℝ).comp_left (g := fun D : KGSpatialSpace →L[ℝ] ℝ => D (kgSpatialDirection i)) (by simp)

theorem spatial_partial_mul (F H : KGSpatialSpace → ℝ) (x : KGSpatialSpace)
    (hF : DifferentiableAt ℝ F x) (hH : DifferentiableAt ℝ H x) (i : Fin 3) :
    spatialPartial (fun y => F y * H y) x i =
      F x * spatialPartial H x i + H x * spatialPartial F x i := by
  have hd := (hF.hasFDerivAt.mul hH.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => F y * H y) x = _ at hd
  simp only [spatialPartial, hd, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem spatial_partial_add_multiple (U d : KGSpatialSpace → ℝ)
    (hU : ContDiff ℝ (⊤ : ℕ∞) U) (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (t : ℝ) (x : KGSpatialSpace) (i : Fin 3) :
    spatialPartial (fun y => U y + t * d y) x i = spatialPartial U x i + t * spatialPartial d x i := by
  have derivative := ((hU.differentiable (by simp) x).hasFDerivAt.add
    ((hd.differentiable (by simp) x).hasFDerivAt.const_mul t)).fderiv
  change fderiv ℝ (fun y => U y + t * d y) x = _ at derivative
  simp [spatialPartial, derivative]

theorem spatial_compact_partial_integral_zero (F : KGSpatialSpace → ℝ)
    (regular : ContDiff ℝ (⊤ : ℕ∞) F) (compact : HasCompactSupport F) (i : Fin 3) :
    (∫ x : KGSpatialSpace, spatialPartial F x i) = 0 := by
  obtain ⟨C, lipschitz⟩ := ContDiff.lipschitzWith_of_hasCompactSupport compact regular (by simp)
  have constantLipschitz : LipschitzWith 0 (fun _ : KGSpatialSpace => (1 : ℝ)) := by
    intro x y
    simp
  have parts := constantLipschitz.integral_lineDeriv_mul_eq
    (μ := (volume : Measure KGSpatialSpace)) lipschitz compact (-(kgSpatialDirection i))
  have constantDerivative (x : KGSpatialSpace) :
      lineDeriv ℝ (fun _ : KGSpatialSpace => (1 : ℝ)) x (-(kgSpatialDirection i)) = 0 := by
    rw [(differentiableAt_const (c := (1 : ℝ))).lineDeriv_eq_fderiv]
    simp
  simp only [constantDerivative, zero_mul, integral_zero, neg_neg, mul_one] at parts
  have actual : (fun x : KGSpatialSpace => lineDeriv ℝ F x (kgSpatialDirection i)) =
      fun x => spatialPartial F x i := by
    funext x
    exact (regular.differentiable (by simp) x).lineDeriv_eq_fderiv
  simpa only [actual] using parts.symm

theorem spatial_compact_integration_by_parts (F d : KGSpatialSpace → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (compact : HasCompactSupport d) (i : Fin 3) :
    (∫ x : KGSpatialSpace, F x * spatialPartial d x i) =
      -(∫ x : KGSpatialSpace, spatialPartial F x i * d x) := by
  have first : Integrable (fun x => F x * spatialPartial d x i) :=
    (hF.continuous.mul (spatial_partial_smooth d hd i).continuous).integrable_of_hasCompactSupport
      ((spatial_partial_compact d compact i).mul_left)
  have second : Integrable (fun x => d x * spatialPartial F x i) :=
    (hd.continuous.mul (spatial_partial_smooth F hF i).continuous).integrable_of_hasCompactSupport compact.mul_right
  have zero := spatial_compact_partial_integral_zero (fun x => F x * d x) (hF.mul hd) compact.mul_left i
  simp_rw [spatial_partial_mul F d _ (hF.differentiable (by simp) _) (hd.differentiable (by simp) _) i] at zero
  rw [integral_add first second] at zero
  have commute : (∫ x : KGSpatialSpace, d x * spatialPartial F x i) =
      (∫ x : KGSpatialSpace, spatialPartial F x i * d x) := by
    congr 1
    funext x
    ring
  rw [commute] at zero
  linarith

end AASCKleinGordon.SameActionSource
