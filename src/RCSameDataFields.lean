import RCLocalTaylor
import KernelFaithfulSameActionKGSource
import EHKGFlatLocalRecovery
import Mathlib.Analysis.Normed.Group.Bounded

/-! Actual same-preparation curved and H=0 fields on a proved common slab.
This is a shrinking-time comparison at fixed a, not a curvature limit. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG AASCKleinGordon.SameActionSource
open scoped Topology
namespace AASCKleinGordon.RecoveryComparison

abbrev flatComparisonField (a : Parameters) (f h : CurvedCauchyDatum a) : CoordinatePoint → ℝ :=
  compactFlatField a (centralLeafDomain (conformalFrequency a)) f h

theorem same_data_initial_values (a : Parameters) (f h : CurvedCauchyDatum a) (x : KGSpatialSpace) :
    sourceField a f h (spaceTimePoint 0 x) = flatComparisonField a f h (spaceTimePoint 0 x) := by
  change compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h (centralLeafPoint x) =
    compactFlatField a (centralLeafDomain (conformalFrequency a)) f h (centralLeafPoint x)
  rw [fixed_mass_flat_initial_position]
  simpa only [central_leaf_space] using compact_curved_initial_position a _ f h _ (central_leaf_time x)

theorem same_data_initial_time_jets (a : Parameters) (f h : CurvedCauchyDatum a) (x : KGSpatialSpace) :
    scalarPartial (sourceField a f h) (spaceTimePoint 0 x) 0 =
      scalarPartial (flatComparisonField a f h) (spaceTimePoint 0 x) 0 := by
  change scalarPartial (sourceField a f h) (centralLeafPoint x) 0 =
    scalarPartial (flatComparisonField a f h) (centralLeafPoint x) 0
  rw [fixed_mass_flat_initial_velocity]
  simpa only [central_leaf_space] using compact_curved_initial_velocity a _ f h _ (central_leaf_time x)

theorem compact_leaf_has_common_slab (a : Parameters) (K : Set KGSpatialSpace)
    (compact : IsCompact K) (interior : K ⊆ centralLeafDomain (conformalFrequency a)) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| ≤ r → ∀ x ∈ K, spaceTimePoint t x ∈ sourceDomain a := by
  rcases K.eq_empty_or_nonempty with empty|nonempty
  · refine ⟨1,by norm_num,?_⟩
    simp [empty]
  · obtain ⟨x0,hx0,maximum⟩ := compact.exists_isMaxOn nonempty continuous_norm.continuousOn
    have margin : ‖x0‖ < protectedRadius (conformalFrequency a) := by
      simpa [centralLeafDomain,Metric.mem_ball,dist_zero_right] using interior hx0
    refine ⟨(protectedRadius (conformalFrequency a)-‖x0‖)/2,by linarith,?_⟩
    intro t ht x hx
    have normBound : ‖x‖ ≤ ‖x0‖ := maximum hx
    change |(spaceTimePoint t x) 0|+‖(coordinateSpatialSplit (spaceTimePoint t x)).2‖ < _
    have time : spaceTimePoint t x 0 = t := by
      change (coordinateSpatialSplit (coordinateSpatialSplit.symm (t,x))).1=t
      simp
    rw [time]
    simp only [spaceTimePoint,ContinuousLinearEquiv.apply_symm_apply]
    linarith

theorem same_data_local_evolved_comparison (a : Parameters) (f h : CurvedCauchyDatum a)
    (K : Set KGSpatialSpace) (compact : IsCompact K)
    (interior : K ⊆ centralLeafDomain (conformalFrequency a)) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
      (∀ t : ℝ, |t| ≤ r → ∀ x ∈ K, spaceTimePoint t x ∈ sourceDomain a) ∧
      ∀ t : ℝ, |t| ≤ r → ∀ x ∈ K,
        |sourceField a f h (spaceTimePoint t x)-flatComparisonField a f h (spaceTimePoint t x)| ≤ C*t^2 ∧
        |scalarPartial (sourceField a f h) (spaceTimePoint t x) 0-
          scalarPartial (flatComparisonField a f h) (spaceTimePoint t x) 0| ≤ C*|t| := by
  obtain ⟨r,hr,slab⟩ := compact_leaf_has_common_slab a K compact interior
  let H : ℝ × KGSpatialSpace → ℝ := fun tx =>
    scalarSecondPartial (sourceField a f h) (spaceTimePoint tx.1 tx.2) 0 0-
      scalarSecondPartial (flatComparisonField a f h) (spaceTimePoint tx.1 tx.2) 0 0
  have regularC := source_field_smooth a f h
  have regularF := fixed_mass_flat_field_smooth a _ f h
  have joined : Continuous (fun tx : ℝ × KGSpatialSpace => spaceTimePoint tx.1 tx.2) :=
    coordinateSpatialSplit.symm.continuous
  have continuousH : Continuous H :=
    ((scalar_second_partial_smooth _ regularC 0 0).continuous.comp joined).sub
      ((scalar_second_partial_smooth _ regularF 0 0).continuous.comp joined)
  have compactSlab : IsCompact (Icc (-r) r ×ˢ K) := isCompact_Icc.prod compact
  obtain ⟨C0,bound⟩ := compactSlab.exists_bound_of_continuousOn (f := H) continuousH.continuousOn
  refine ⟨r,|C0|,hr,abs_nonneg _,slab,?_⟩
  intro t ht x hx
  have estimate := zero_jet_second_order_bound
    (fun s => sourceField a f h (spaceTimePoint s x)-flatComparisonField a f h (spaceTimePoint s x))
    (fun s => scalarPartial (sourceField a f h) (spaceTimePoint s x) 0-
      scalarPartial (flatComparisonField a f h) (spaceTimePoint s x) 0)
    (fun s => H (s,x)) r |C0| hr.le (abs_nonneg _)
    (fun s => (scalar_join_time_hasDerivAt _ regularC s x).sub (scalar_join_time_hasDerivAt _ regularF s x))
    (fun s => (scalar_join_time_hasDerivAt _ (scalar_partial_smooth _ regularC 0) s x).sub
      (scalar_join_time_hasDerivAt _ (scalar_partial_smooth _ regularF 0) s x))
    (fun s hs => (show |H (s,x)| ≤ C0 by simpa only [Real.norm_eq_abs] using bound (s,x) ⟨abs_le.mp hs,hx⟩).trans (le_abs_self C0))
    (sub_eq_zero.mpr (same_data_initial_values a f h x))
    (sub_eq_zero.mpr (same_data_initial_time_jets a f h x)) t ht
  exact ⟨estimate.2,estimate.1⟩

end AASCKleinGordon.RecoveryComparison
