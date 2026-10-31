import SKGSourceOccupation
import SKGSpatialSlice

/-! The same covariant stress supplies canonical energy and momentum.
Coordinate time is x0=c*t; normal and coordinate densities differ by lapse. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

def scalarSourceLapse (a : Parameters) (p : CoordinatePoint) : ℝ := Real.sqrt (sourceFactor a p)
def scalarSourceNormal (a : Parameters) (p : CoordinatePoint) : CoordinatePoint :=
  Pi.single 0 (scalarSourceLapse a p)⁻¹
def scalarSpatialVolume (a : Parameters) (p : CoordinatePoint) : ℝ := sourceFactor a p * scalarSourceLapse a p
def scalarNormalEnergy (a : Parameters) (u : CoordinatePoint → ℝ) (p : CoordinatePoint) : ℝ :=
  sameSourceStress a u p 0 0 / sourceFactor a p
def scalarNormalMomentum (a : Parameters) (u : CoordinatePoint → ℝ) (p : CoordinatePoint) (i : Fin 3) : ℝ :=
  -sameSourceStress a u p 0 i.succ / scalarSourceLapse a p
def scalarSpatialStress (a : Parameters) (u : CoordinatePoint → ℝ) (p : CoordinatePoint) (i j : Fin 3) : ℝ :=
  sameSourceStress a u p i.succ j.succ

theorem scalar_source_lapse_positive (a : Parameters) (p : CoordinatePoint) :
    0 < scalarSourceLapse a p := Real.sqrt_pos.mpr (source_factor_positive a p)

theorem scalar_source_normal_unit (a : Parameters) (p : CoordinatePoint) :
    coordinateMetricPairing (sourceMetric a p) (scalarSourceNormal a p) (scalarSourceNormal a p) = -1 := by
  have square : scalarSourceLapse a p ^ 2 = sourceFactor a p := Real.sq_sqrt (le_of_lt (source_factor_positive a p))
  rw [source_metric_conformal]
  simp [coordinateMetricPairing, scalarSourceNormal, scalarConformalMetric, metric,
    Matrix.diagonal_apply, Fin.sum_univ_succ]
  field_simp [ne_of_gt (scalar_source_lapse_positive a p)]
  nlinarith [square]

theorem scalar_normal_energy_is_actual_contraction (a : Parameters) (u : CoordinatePoint → ℝ)
    (p : CoordinatePoint) :
    scalarNormalEnergy a u p =
      ∑ i : Fin 4, ∑ j : Fin 4, scalarSourceNormal a p i * scalarSourceNormal a p j * sameSourceStress a u p i j := by
  have square : scalarSourceLapse a p ^ 2 = sourceFactor a p := Real.sq_sqrt (le_of_lt (source_factor_positive a p))
  simp [scalarSourceNormal, Fin.sum_univ_succ]
  unfold scalarNormalEnergy
  field_simp [source_factor_nonzero a p, ne_of_gt (scalar_source_lapse_positive a p)]
  rw [square]

theorem scalar_normal_momentum_is_actual_contraction (a : Parameters) (u : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (i : Fin 3) :
    scalarNormalMomentum a u p i =
      -(∑ j : Fin 4, scalarSourceNormal a p j * sameSourceStress a u p j i.succ) := by
  simp [scalarNormalMomentum, scalarSourceNormal, Fin.sum_univ_succ, div_eq_mul_inv]
  ring

theorem actual_scalar_hamiltonian_is_time_energy (a : Parameters) (u : CoordinatePoint → ℝ)
    (p : CoordinatePoint) :
    actualScalarHamiltonianDensity a u (actualScalarCanonicalMomentum a u) p =
      sourceFactor a p ^ 2 * scalarNormalEnergy a u p := by
  unfold actualScalarHamiltonianDensity scalarNormalEnergy actualScalarCanonicalMomentum scalarCanonicalMomentum
  rw [same_source_time_time]
  unfold scalarCanonicalHamiltonian
  field_simp [source_factor_nonzero a p]
  <;> ring

theorem scalar_normal_hamiltonian_lapse (a : Parameters) (u : CoordinatePoint → ℝ)
    (p : CoordinatePoint) :
    actualScalarHamiltonianDensity a u (actualScalarCanonicalMomentum a u) p =
      scalarSourceLapse a p * (scalarSpatialVolume a p * scalarNormalEnergy a u p) := by
  rw [actual_scalar_hamiltonian_is_time_energy]
  have square : scalarSourceLapse a p ^ 2 = sourceFactor a p := Real.sq_sqrt (le_of_lt (source_factor_positive a p))
  unfold scalarSpatialVolume
  calc
    sourceFactor a p ^ 2 * scalarNormalEnergy a u p =
        sourceFactor a p * (scalarSourceLapse a p ^ 2) * scalarNormalEnergy a u p := by rw [square]; ring
    _ = _ := by ring

theorem scalar_stress_time_spatial (a : Parameters) (u : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (i : Fin 3) :
    sameSourceStress a u p 0 i.succ = scalarPartial u p 0 * scalarPartial u p i.succ := by
  rw [sameSourceStress, source_metric_conformal,
    scalar_conformal_stress_polynomial _ u _ p (source_factor_nonzero a p)]
  fin_cases i <;> simp [scalarConformalStressPolynomial, metric, Matrix.diagonal_apply]

theorem scalar_canonical_momentum_projection (a : Parameters) (u : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (i : Fin 3) :
    actualScalarCanonicalMomentum a u p * scalarPartial u p i.succ =
      -scalarSpatialVolume a p * scalarNormalMomentum a u p i := by
  rw [scalarNormalMomentum, scalar_stress_time_spatial]
  unfold actualScalarCanonicalMomentum scalarCanonicalMomentum scalarSpatialVolume
  field_simp [ne_of_gt (scalar_source_lapse_positive a p)]
  <;> ring

theorem scalar_spatial_stress_projection (a : Parameters) (u : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (i j : Fin 3) :
    scalarSpatialStress a u p i j = scalarPartial u p i.succ * scalarPartial u p j.succ -
      (1 / 2 : ℝ) * sourceMetric a p i.succ j.succ *
        (scalarFieldKinetic (sourceMetric a) u p + massWaveNumber a ^ 2 * (u p * u p)) := by
  unfold scalarSpatialStress sameSourceStress scalarFieldStress
  ring

theorem scalar_physical_time_derivative (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ (⊤ : ℕ∞) u) (t : ℝ) (x : KGSpatialSpace) :
    HasDerivAt (fun r : ℝ => u (spaceTimePoint (a.speed * r) x))
      (a.speed * scalarPartial u (spaceTimePoint (a.speed * t) x) 0) t := by
  have derivative := (scalar_join_time_hasDerivAt u regular (a.speed * t) x).comp t
    ((hasDerivAt_id t).const_mul a.speed)
  convert derivative using 1 <;> simp <;> ring

end AASCKleinGordon.SameActionSource
