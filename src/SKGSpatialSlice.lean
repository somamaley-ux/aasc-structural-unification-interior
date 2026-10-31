import SKGSpatialHamiltonian

/-! The generic spatial functional is attached to actual slices of the
same curved scalar field and the same metric factor. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

def scalarSpatialSlice (F : CoordinatePoint → ℝ) (t : ℝ) : KGSpatialSpace → ℝ :=
  fun x => F (spaceTimePoint t x)

theorem scalar_spatial_slice_smooth (F : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ (⊤ : ℕ∞) F) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (scalarSpatialSlice F t) := by
  exact regular.comp (coordinateSpatialSplit.symm.toContinuousLinearMap.contDiff.comp
    (contDiff_const.prodMk contDiff_id))

theorem scalar_spatial_slice_partial (F : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ (⊤ : ℕ∞) F) (t : ℝ) (x : KGSpatialSpace) (i : Fin 3) :
    spatialPartial (scalarSpatialSlice F t) x i = scalarPartial F (spaceTimePoint t x) i.succ :=
  scalar_join_spatial_partial F regular t x i

theorem scalar_slice_euler_is_actual (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ (⊤ : ℕ∞) u) (t : ℝ) (x : KGSpatialSpace) :
    spatialHamiltonianEuler (scalarSpatialSlice (sourceFactor a) t) (scalarSpatialSlice u t)
      (massWaveNumber a ^ 2) x = actualScalarHamiltonianEuler a u (spaceTimePoint t x) := by
  have flux (i : Fin 3) :
      (fun y => scalarSpatialSlice (sourceFactor a) t y * spatialPartial (scalarSpatialSlice u t) y i) =
      scalarSpatialSlice (fun q => sourceFactor a q * scalarPartial u q i.succ) t := by
    funext y
    rw [scalar_spatial_slice_partial u regular]
    rfl
  unfold spatialHamiltonianEuler actualScalarHamiltonianEuler
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [flux i]
  exact scalar_spatial_slice_partial _ ((source_factor_smooth a).mul (scalar_partial_smooth u regular i.succ)) t x i

theorem actual_scalar_spatial_hamiltonian_derivative (a : Parameters) (u pi : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ (⊤ : ℕ∞) u) (t : ℝ) (d : KGSpatialSpace → ℝ)
    (regularD : ContDiff ℝ (⊤ : ℕ∞) d) (compactD : HasCompactSupport d) :
    HasDerivAt (spatialHamiltonianRelative (scalarSpatialSlice (sourceFactor a) t)
      (scalarSpatialSlice u t) (scalarSpatialSlice pi t) d (massWaveNumber a ^ 2))
      (∫ x : KGSpatialSpace, actualScalarHamiltonianEuler a u (spaceTimePoint t x) * d x) 0 := by
  have derivative := spatial_hamiltonian_euler_derivative (scalarSpatialSlice (sourceFactor a) t)
    (scalarSpatialSlice u t) (scalarSpatialSlice pi t) d
    (scalar_spatial_slice_smooth _ (source_factor_smooth a) t)
    (scalar_spatial_slice_smooth u regular t) regularD compactD (massWaveNumber a ^ 2)
  simpa only [scalar_slice_euler_is_actual a u regular t] using derivative

theorem constructed_scalar_spatial_hamiltonian_force (a : Parameters) (f h : CurvedCauchyDatum a)
    (t : ℝ) (d : KGSpatialSpace → ℝ) (regularD : ContDiff ℝ (⊤ : ℕ∞) d)
    (compactD : HasCompactSupport d)
    (inside : ∀ x ∈ tsupport d, spaceTimePoint t x ∈ sourceDomain a) :
    HasDerivAt (spatialHamiltonianRelative (scalarSpatialSlice (sourceFactor a) t)
      (scalarSpatialSlice (sourceField a f h) t)
      (scalarSpatialSlice (actualScalarCanonicalMomentum a (sourceField a f h)) t) d (massWaveNumber a ^ 2))
      (-(∫ x : KGSpatialSpace,
        scalarPartial (actualScalarCanonicalMomentum a (sourceField a f h)) (spaceTimePoint t x) 0 * d x)) 0 := by
  have derivative := actual_scalar_spatial_hamiltonian_derivative a (sourceField a f h)
    (actualScalarCanonicalMomentum a (sourceField a f h)) (source_field_smooth a f h) t d regularD compactD
  have pairing : (∫ x : KGSpatialSpace, actualScalarHamiltonianEuler a (sourceField a f h) (spaceTimePoint t x) * d x) =
      -(∫ x : KGSpatialSpace,
        scalarPartial (actualScalarCanonicalMomentum a (sourceField a f h)) (spaceTimePoint t x) 0 * d x) := by
    rw [← integral_neg]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    change actualScalarHamiltonianEuler a (sourceField a f h) (spaceTimePoint t x) * d x =
      -(scalarPartial (actualScalarCanonicalMomentum a (sourceField a f h)) (spaceTimePoint t x) 0 * d x)
    by_cases nonzero : d x = 0
    · simp [nonzero]
    · have equation := constructed_scalar_second_hamilton_equation a f h (spaceTimePoint t x)
        (inside x (subset_tsupport d nonzero))
      rw [equation]
      ring
  rw [pairing] at derivative
  exact derivative

end AASCKleinGordon.SameActionSource
