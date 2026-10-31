import SKGScalarLegendre

/-! The actual momentum history and spatial Euler expression reproduce the
same KG equation. Coordinate-time is x0; background work is not suppressed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

def actualScalarCanonicalMomentum (a : Parameters) (u : CoordinatePoint → ℝ)
    (p : CoordinatePoint) : ℝ := scalarCanonicalMomentum (sourceFactor a p) (scalarPartial u p 0)

def actualScalarHamiltonianDensity (a : Parameters) (u pi : CoordinatePoint → ℝ)
    (p : CoordinatePoint) : ℝ :=
  scalarCanonicalHamiltonian (sourceFactor a p) (massWaveNumber a ^ 2) (u p) (pi p)
    (fun i => scalarPartial u p i.succ)

def actualScalarHamiltonianEuler (a : Parameters) (u : CoordinatePoint → ℝ)
    (p : CoordinatePoint) : ℝ := massWaveNumber a ^ 2 * sourceFactor a p ^ 2 * u p -
      ∑ i : Fin 3, scalarPartial (fun q => sourceFactor a q * scalarPartial u q i.succ) p i.succ

theorem actual_scalar_first_hamilton_equation (a : Parameters) (u : CoordinatePoint → ℝ)
    (p : CoordinatePoint) :
    scalarPartial u p 0 = deriv (fun pi : ℝ => scalarCanonicalHamiltonian (sourceFactor a p)
      (massWaveNumber a ^ 2) (u p) pi (fun i => scalarPartial u p i.succ))
        (actualScalarCanonicalMomentum a u p) := by
  rw [(scalar_hamiltonian_momentum_derivative _ _ _ _ _).deriv]
  simp [actualScalarCanonicalMomentum, scalarCanonicalMomentum, source_factor_nonzero a p]

theorem actual_scalar_hamiltonian_residual (a : Parameters) (u : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (regularU : ContDiffAt ℝ 2 u p) :
    scalarPartial (actualScalarCanonicalMomentum a u) p 0 + actualScalarHamiltonianEuler a u p =
      -(sourceFactor a p ^ 2) *
        (scalarFieldWaveOperator (sourceMetric a) u p - massWaveNumber a ^ 2 * u p) := by
  have regularL : DifferentiableAt ℝ (sourceFactor a) p :=
    (source_factor_smooth a).differentiable (by simp) p
  have fluxPartial (i : Fin 4) :
      scalarPartial (fun q => sourceFactor a q * scalarPartial u q i) p i =
        sourceFactor a p * scalarSecondPartial u p i i + scalarPartial u p i * scalarPartial (sourceFactor a) p i := by
    rw [skg_partial_mul (sourceFactor a) (fun q => scalarPartial u q i) p regularL
      (c2_local_scalarPartial_differentiableAt u p regularU i) i]
    rfl
  change scalarPartial (fun q => sourceFactor a q * scalarPartial u q 0) p 0 +
    (massWaveNumber a ^ 2 * sourceFactor a p ^ 2 * u p -
      ∑ i : Fin 3, scalarPartial (fun q => sourceFactor a q * scalarPartial u q i.succ) p i.succ) = _
  simp_rw [fluxPartial]
  rw [source_metric_conformal, scalar_conformal_wave_operator _ u p regularL (source_factor_nonzero a p)]
  simp [metric, Matrix.diagonal_apply, Fin.sum_univ_succ]
  field_simp [source_factor_nonzero a p]
  <;> ring

theorem scalar_hamilton_equations_iff_same_kg (a : Parameters) (u : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (regularU : ContDiffAt ℝ 2 u p) :
    (scalarPartial u p 0 = deriv (fun pi : ℝ => scalarCanonicalHamiltonian (sourceFactor a p)
        (massWaveNumber a ^ 2) (u p) pi (fun i => scalarPartial u p i.succ))
          (actualScalarCanonicalMomentum a u p) ∧
      scalarPartial (actualScalarCanonicalMomentum a u) p 0 = -actualScalarHamiltonianEuler a u p) ↔
      scalarFieldWaveOperator (sourceMetric a) u p = massWaveNumber a ^ 2 * u p := by
  have residual := actual_scalar_hamiltonian_residual a u p regularU
  constructor
  · rintro ⟨_, second⟩
    have zero : -(sourceFactor a p ^ 2) *
        (scalarFieldWaveOperator (sourceMetric a) u p - massWaveNumber a ^ 2 * u p) = 0 := by
      rw [← residual, second]
      ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left
      (neg_ne_zero.mpr (pow_ne_zero 2 (source_factor_nonzero a p))))
  · intro equation
    refine ⟨actual_scalar_first_hamilton_equation a u p, ?_⟩
    rw [equation, sub_self, mul_zero] at residual
    exact eq_neg_of_add_eq_zero_left residual

theorem constructed_scalar_second_hamilton_equation (a : Parameters) (f h : CurvedCauchyDatum a)
    (p : CoordinatePoint) (inside : p ∈ sourceDomain a) :
    scalarPartial (actualScalarCanonicalMomentum a (sourceField a f h)) p 0 =
      -actualScalarHamiltonianEuler a (sourceField a f h) p :=
  ((scalar_hamilton_equations_iff_same_kg a _ p
    ((source_field_smooth a f h).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))).mpr
        (source_field_equation a f h p inside)).2

end AASCKleinGordon.SameActionSource
