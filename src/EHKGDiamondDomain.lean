import EHKGCompactCauchyData

/-! An actual open diamond inside the protected chart, its central spatial
leaf and the unit future normal of the same original EH metric. Causal-curve
and Cauchy properties are proved in later modules; openness is not promoted
to global hyperbolicity here. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped SchwartzMap Topology BigOperators
namespace AASCKleinGordon.CurvedKG

def diamondGauge (p : CoordinatePoint) : ℝ := |p 0| + ‖(coordinateSpatialSplit p).2‖

theorem diamond_gauge_continuous : Continuous diamondGauge := by
  exact (continuous_apply (0 : Fin 4)).abs.add (continuous_snd.comp coordinateSpatialSplit.continuous).norm

theorem coordinate_norm_le_diamond_gauge (p : CoordinatePoint) : ‖p‖ ≤ diamondGauge p := by
  apply (pi_norm_le_iff_of_nonneg (by dsimp [diamondGauge]; positivity)).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Real.norm_eq_abs, diamondGauge] using le_add_of_nonneg_right (norm_nonneg ((coordinateSpatialSplit p).2))
  · have component := PiLp.norm_apply_le (coordinateSpatialSplit p).2 j
    have equal : (coordinateSpatialSplit p).2 j = p j.succ := rfl
    rw [equal] at component
    exact component.trans (le_add_of_nonneg_left (abs_nonneg _))

def protectedDiamond (nu : ℝ) : Set CoordinatePoint :=
  {p | diamondGauge p < protectedRadius nu}

theorem protected_diamond_open (nu : ℝ) : IsOpen (protectedDiamond nu) :=
  isOpen_lt diamond_gauge_continuous continuous_const

theorem protected_diamond_zero (nu : ℝ) : (0 : CoordinatePoint) ∈ protectedDiamond nu := by
  simpa [protectedDiamond, diamondGauge] using protected_radius_positive nu

theorem protected_diamond_subset_ball (nu : ℝ) :
    protectedDiamond nu ⊆ protectedConformalBall nu := by
  intro p hp
  change dist p 0 < protectedRadius nu
  rw [dist_zero_right]
  exact (coordinate_norm_le_diamond_gauge p).trans_lt hp

def centralLeafDomain (nu : ℝ) : Opens KGSpatialSpace :=
  ⟨Metric.ball 0 (protectedRadius nu), Metric.isOpen_ball⟩

def centralLeafPoint (x : KGSpatialSpace) : CoordinatePoint := coordinateSpatialSplit.symm (0, x)

theorem central_leaf_time (x : KGSpatialSpace) : centralLeafPoint x 0 = 0 := by
  change (coordinateSpatialSplit (centralLeafPoint x)).1 = 0
  simp [centralLeafPoint]

theorem central_leaf_space (x : KGSpatialSpace) :
    (coordinateSpatialSplit (centralLeafPoint x)).2 = x := by simp [centralLeafPoint]

theorem central_leaf_in_diamond_iff (nu : ℝ) (x : KGSpatialSpace) :
    centralLeafPoint x ∈ protectedDiamond nu ↔ x ∈ centralLeafDomain nu := by
  simp [protectedDiamond, diamondGauge, central_leaf_time, central_leaf_space,
    centralLeafDomain, Metric.mem_ball, dist_zero_right]

def timeUnitNormal (nu : ℝ) (p : CoordinatePoint) : CoordinatePoint :=
  Real.cos (nu * p 0) • (Pi.single (0 : Fin 4) (1 : ℝ) : CoordinatePoint)

def actualNormalDerivative (nu : ℝ) (u : CoordinatePoint → ℝ) (p : CoordinatePoint) : ℝ :=
  fderiv ℝ u p (timeUnitNormal nu p)

theorem time_unit_normal_smooth (nu : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (timeUnitNormal nu) := by
  have linear : ContDiff ℝ (⊤ : ℕ∞) (fun p : CoordinatePoint => nu * p 0) := by fun_prop
  exact linear.cos.smul contDiff_const

theorem time_unit_normal_future (nu : ℝ) (p : CoordinatePoint)
    (inside : p ∈ protectedDiamond nu) : 0 < timeUnitNormal nu p 0 := by
  simpa [timeUnitNormal, Pi.single_apply] using
    protected_cosine_positive nu p (protected_diamond_subset_ball nu inside)

theorem time_unit_normal_unit (nu : ℝ) (p : CoordinatePoint)
    (inside : p ∈ protectedDiamond nu) :
    wickMatrixQuadratic (originalEHActMetric (conformalOperand nu) p) (timeUnitNormal nu p) = -1 := by
  rw [protected_metric_identity nu p (protected_diamond_subset_ball nu inside)]
  have safe := ne_of_gt (protected_cosine_positive nu p (protected_diamond_subset_ball nu inside))
  simp [timeConformalMetric, quadratic_scalar_multiple, wickMatrixQuadratic, timeUnitNormal,
    Fin.sum_univ_succ, Pi.single_apply, secantScale, metric, Matrix.diagonal_apply]
  field_simp

def coordinateMetricPairing (M : Tensor2) (v w : CoordinatePoint) : ℝ :=
  ∑ i, ∑ j, v i * M i j * w j

theorem time_unit_normal_orthogonal (nu : ℝ) (p v : CoordinatePoint)
    (inside : p ∈ protectedDiamond nu) (spatial : v 0 = 0) :
    coordinateMetricPairing (originalEHActMetric (conformalOperand nu) p) (timeUnitNormal nu p) v = 0 := by
  rw [protected_metric_identity nu p (protected_diamond_subset_ball nu inside)]
  simp [coordinateMetricPairing, timeConformalMetric, timeUnitNormal, Fin.sum_univ_succ,
    Pi.single_apply, metric, Matrix.diagonal_apply, spatial]

theorem constant_time_slice_spacelike (nu : ℝ) (p v : CoordinatePoint)
    (inside : p ∈ protectedDiamond nu) (spatial : v 0 = 0) (nonzero : v ≠ 0) :
    0 < wickMatrixQuadratic (originalEHActMetric (conformalOperand nu) p) v := by
  rw [conformal_operand_actual_metric, quadratic_scalar_multiple, flat_quadratic_value, spatial]
  have tailNonzero : Fin.tail v ≠ 0 := by
    intro h
    apply nonzero
    funext i
    exact Fin.cases spatial (fun j => congrFun h j) i
  simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), neg_zero, zero_add] using
    mul_pos (conformal_metric_factor_positive nu p) (wick_spatial_square_pos _ tailNonzero)

theorem central_normal_is_coordinate (nu : ℝ) (x : KGSpatialSpace) :
    timeUnitNormal nu (centralLeafPoint x) = Pi.single (0 : Fin 4) (1 : ℝ) := by
  simp [timeUnitNormal, central_leaf_time]

theorem compact_curved_initial_normal (a : Parameters)
    (f h : TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞))
    (x : KGSpatialSpace) :
    actualNormalDerivative (conformalFrequency a)
      (compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h) (centralLeafPoint x) = h x := by
  rw [actualNormalDerivative, central_normal_is_coordinate]
  change scalarPartial _ _ 0 = _
  simpa only [central_leaf_space] using compact_curved_initial_velocity a _ f h
    (centralLeafPoint x) (central_leaf_time x)

end AASCKleinGordon.CurvedKG
