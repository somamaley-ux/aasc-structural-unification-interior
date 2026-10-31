import EHKGWindowedEnergy

/-! Actual first-order variables and derivatives of an arbitrary globally
smooth scalar comparison field. These are constructed from its derivatives;
no compatible-gradient or first-order-solution certificate is received. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology BigOperators
namespace AASCKleinGordon.CurvedKG

def spaceTimePoint (t : ℝ) (x : KGSpatialSpace) : CoordinatePoint := coordinateSpatialSplit.symm (t, x)

theorem join_time_direction : coordinateSpatialSplit.symm (1, 0) = (Pi.single (0 : Fin 4) (1 : ℝ) : CoordinatePoint) := by
  apply coordinateSpatialSplit.injective
  simpa using (coordinate_split_time_curve (0 : CoordinatePoint) 1).symm

theorem join_spatial_direction (i : Fin 3) :
    coordinateSpatialSplit.symm (0, kgSpatialDirection i) = (Pi.single i.succ (1 : ℝ) : CoordinatePoint) := by
  apply coordinateSpatialSplit.injective
  simpa using (coordinate_split_space_curve (0 : CoordinatePoint) 1 i).symm

theorem scalar_partial_smooth (F : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) F) (c : Fin 4) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => scalarPartial F p c) := by
  exact (regular.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem scalar_second_partial_smooth (F : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) F) (c d : Fin 4) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => scalarSecondPartial F p c d) :=
  scalar_partial_smooth _ (scalar_partial_smooth F regular c) d

theorem scalar_join_time_hasDerivAt (F : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) F)
    (t : ℝ) (x : KGSpatialSpace) :
    HasDerivAt (fun s => F (spaceTimePoint s x)) (scalarPartial F (spaceTimePoint t x) 0) t := by
  have param := (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have joined := coordinateSpatialSplit.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t param
  have actual := (regular.differentiable (by simp) (spaceTimePoint t x)).hasFDerivAt.comp_hasDerivAt t joined
  change HasDerivAt (fun s => F (spaceTimePoint s x))
    (fderiv ℝ F (spaceTimePoint t x) (coordinateSpatialSplit.symm (1, 0))) t at actual
  rw [join_time_direction] at actual
  exact actual

theorem scalar_join_spatial_partial (F : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) F)
    (t : ℝ) (x : KGSpatialSpace) (i : Fin 3) :
    fderiv ℝ (fun y => F (spaceTimePoint t y)) x (kgSpatialDirection i) = scalarPartial F (spaceTimePoint t x) i.succ := by
  have param := (hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id x)
  have joined := coordinateSpatialSplit.symm.toContinuousLinearMap.hasFDerivAt.comp x param
  have actual := (regular.differentiable (by simp) (spaceTimePoint t x)).hasFDerivAt.comp x joined
  have actualDerivative := actual.fderiv
  change fderiv ℝ (fun y => F (spaceTimePoint t y)) x = _ at actualDerivative
  rw [actualDerivative]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply, scalarPartial]
  change fderiv ℝ F (spaceTimePoint t x) (coordinateSpatialSplit.symm (0, kgSpatialDirection i)) = _
  rw [join_spatial_direction]

def jetPosition (F : CoordinatePoint → ℝ) (t : ℝ) (x : KGSpatialSpace) : ℝ := F (spaceTimePoint t x)
def jetVelocity (F : CoordinatePoint → ℝ) (t : ℝ) (x : KGSpatialSpace) : ℝ := scalarPartial F (spaceTimePoint t x) 0
def jetGradient (F : CoordinatePoint → ℝ) (t : ℝ) (x : KGSpatialSpace) : KGSpatialSpace :=
  momentumEuclidean (fun i => scalarPartial F (spaceTimePoint t x) i.succ)
def jetVelocityGradient (F : CoordinatePoint → ℝ) (t : ℝ) (x : KGSpatialSpace) : KGSpatialSpace :=
  momentumEuclidean (fun i => scalarSecondPartial F (spaceTimePoint t x) 0 i.succ)

theorem jet_position_time (F : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) F)
    (t : ℝ) (x : KGSpatialSpace) : HasDerivAt (fun s => jetPosition F s x) (jetVelocity F t x) t :=
  scalar_join_time_hasDerivAt F regular t x

theorem jet_velocity_time (F : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) F)
    (t : ℝ) (x : KGSpatialSpace) :
    HasDerivAt (fun s => jetVelocity F s x) (scalarSecondPartial F (spaceTimePoint t x) 0 0) t :=
  scalar_join_time_hasDerivAt _ (scalar_partial_smooth F regular 0) t x

theorem jet_gradient_time (F : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) F)
    (t : ℝ) (x : KGSpatialSpace) : HasDerivAt (fun s => jetGradient F s x) (jetVelocityGradient F t x) t := by
  apply momentumEuclidean.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
  apply hasDerivAt_pi.mpr
  intro i
  have actual := scalar_join_time_hasDerivAt _ (scalar_partial_smooth F regular i.succ) t x
  rw [show scalarPartial (fun p => scalarPartial F p i.succ) (spaceTimePoint t x) 0 =
    scalarSecondPartial F (spaceTimePoint t x) 0 i.succ from
      c2_scalarSecondPartial_symmetric F _ (regular.contDiffAt.of_le
        (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) i.succ 0] at actual
  exact actual

theorem jet_velocity_spatial_partial (F : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) F)
    (t : ℝ) (x : KGSpatialSpace) (i : Fin 3) :
    fderiv ℝ (jetVelocity F t) x (kgSpatialDirection i) = jetVelocityGradient F t x i :=
  scalar_join_spatial_partial _ (scalar_partial_smooth F regular 0) t x i

theorem jet_gradient_divergence (F : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) F)
    (t : ℝ) (x : KGSpatialSpace) :
    kgSpatialDivergence (jetGradient F t) x = scalarSecondPartial F (spaceTimePoint t x) 1 1 +
      scalarSecondPartial F (spaceTimePoint t x) 2 2 + scalarSecondPartial F (spaceTimePoint t x) 3 3 := by
  unfold kgSpatialDivergence
  have component (i : Fin 3) :
      fderiv ℝ (fun y => jetGradient F t y i) x (kgSpatialDirection i) = scalarSecondPartial F (spaceTimePoint t x) i.succ i.succ :=
    scalar_join_spatial_partial _ (scalar_partial_smooth F regular i.succ) t x i
  simp only [component, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.reduceSucc]
  ring

end AASCKleinGordon.CurvedKG
