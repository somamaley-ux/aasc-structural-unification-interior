import EHKGDiamondCauchyLeaf

/-! Explicit coordinate foliation, lapse and shift of the constructed metric.
The central leaf is Cauchy on the diamond. Other constant-time sections are
spacelike foliation sections; they are not asserted Cauchy for the whole
diamond. Continuation must use its appropriate dependence domains. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

def evolutionTimeRange (nu : ℝ) : Set ℝ := Ioo (-protectedRadius nu) (protectedRadius nu)

def evolutionSliceDomain (nu t : ℝ) : Opens KGSpatialSpace :=
  ⟨Metric.ball 0 (protectedRadius nu - |t|), Metric.isOpen_ball⟩

def evolutionSlicePoint (t : ℝ) (x : KGSpatialSpace) : CoordinatePoint :=
  coordinateSpatialSplit.symm (t, x)

theorem evolution_slice_time (t : ℝ) (x : KGSpatialSpace) : evolutionSlicePoint t x 0 = t := by
  change (coordinateSpatialSplit (coordinateSpatialSplit.symm (t, x))).1 = t
  rw [coordinateSpatialSplit.apply_symm_apply]

theorem evolution_slice_space (t : ℝ) (x : KGSpatialSpace) :
    (coordinateSpatialSplit (evolutionSlicePoint t x)).2 = x := by
  rw [evolutionSlicePoint, coordinateSpatialSplit.apply_symm_apply]

theorem evolution_slice_in_diamond (nu t : ℝ) (x : KGSpatialSpace) :
    evolutionSlicePoint t x ∈ protectedDiamond nu ↔ x ∈ evolutionSliceDomain nu t := by
  change |evolutionSlicePoint t x 0| + ‖(coordinateSpatialSplit (evolutionSlicePoint t x)).2‖ <
    protectedRadius nu ↔ dist x 0 < protectedRadius nu - |t|
  rw [evolution_slice_time, evolution_slice_space, dist_zero_right]
  exact lt_sub_iff_add_lt'.symm

theorem diamond_time_in_range (nu : ℝ) (p : CoordinatePoint) (inside : p ∈ protectedDiamond nu) :
    p 0 ∈ evolutionTimeRange nu := by
  have h : |p 0| < protectedRadius nu :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans_lt inside
  exact abs_lt.mp h

theorem diamond_foliated_by_slices (nu : ℝ) (p : CoordinatePoint) (inside : p ∈ protectedDiamond nu) :
    ∃ t ∈ evolutionTimeRange nu, ∃ x ∈ evolutionSliceDomain nu t,
      p = evolutionSlicePoint t x := by
  refine ⟨p 0, diamond_time_in_range nu p inside, (coordinateSpatialSplit p).2, ?_, ?_⟩
  · apply (evolution_slice_in_diamond nu (p 0) _).mp
    have same : evolutionSlicePoint (p 0) (coordinateSpatialSplit p).2 = p := by
      change coordinateSpatialSplit.symm (coordinateSpatialSplit p) = p
      exact coordinateSpatialSplit.symm_apply_apply p
    rwa [same]
  · change p = coordinateSpatialSplit.symm (coordinateSpatialSplit p)
    exact (coordinateSpatialSplit.symm_apply_apply p).symm

def evolutionLapse (nu : ℝ) (p : CoordinatePoint) : ℝ := secantScale nu (p 0)

def evolutionShift (_nu : ℝ) (_p : CoordinatePoint) : KGSpatialSpace := 0

theorem evolution_lapse_positive (nu : ℝ) (p : CoordinatePoint) (inside : p ∈ protectedDiamond nu) :
    0 < evolutionLapse nu p :=
  inv_pos.mpr (protected_cosine_positive _ _ (protected_diamond_subset_ball _ inside))

theorem evolution_lapse_smooth (nu : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (evolutionLapse nu) (protectedDiamond nu) := by
  have linear : ContDiff ℝ (⊤ : ℕ∞) (fun p : CoordinatePoint => nu * p 0) := by fun_prop
  exact linear.contDiffOn.cos.inv (fun p hp =>
    ne_of_gt (protected_cosine_positive _ _ (protected_diamond_subset_ball _ hp)))

theorem evolution_shift_smooth (nu : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (evolutionShift nu) := contDiff_const

theorem coordinate_time_is_lapse_normal (nu : ℝ) (p : CoordinatePoint)
    (inside : p ∈ protectedDiamond nu) :
    (Pi.single (0 : Fin 4) (1 : ℝ) : CoordinatePoint) = evolutionLapse nu p • timeUnitNormal nu p := by
  rw [timeUnitNormal, smul_smul]
  have safe := ne_of_gt (protected_cosine_positive _ _ (protected_diamond_subset_ball _ inside))
  simp [evolutionLapse, secantScale, safe]

theorem coordinate_time_normal_derivative (nu : ℝ) (u : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (inside : p ∈ protectedDiamond nu) :
    scalarPartial u p 0 = evolutionLapse nu p * actualNormalDerivative nu u p := by
  change fderiv ℝ u p (Pi.single 0 1) = _
  rw [coordinate_time_is_lapse_normal nu p inside, map_smul]
  rfl

theorem zero_slice_is_declared_cauchy_leaf (nu : ℝ) :
    evolutionSliceDomain nu 0 = centralLeafDomain nu ∧
      evolutionSlicePoint 0 = centralLeafPoint := by
  constructor
  · apply Opens.ext
    simp [evolutionSliceDomain, centralLeafDomain]
  · rfl

end AASCKleinGordon.CurvedKG
