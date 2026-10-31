import SKGScalarHamiltonian

/-! Independent canonical momentum is not silently defined to be the
Legendre momentum. Equality on an open region is derived from Hamilton's
first equation before transporting its actual derivative. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

def ScalarHamiltonPairOn (a : Parameters) (u pi : CoordinatePoint → ℝ)
    (D : Opens CoordinatePoint) : Prop :=
  (∀ p ∈ D, scalarPartial u p 0 = pi p / sourceFactor a p) ∧
    ∀ p ∈ D, scalarPartial pi p 0 = -actualScalarHamiltonianEuler a u p

theorem scalar_momentum_derivative_local (a : Parameters) (u pi : CoordinatePoint → ℝ)
    (D : Opens CoordinatePoint) (same : EqOn pi (actualScalarCanonicalMomentum a u) D)
    (p : CoordinatePoint) (inside : p ∈ D) :
    scalarPartial pi p 0 = scalarPartial (actualScalarCanonicalMomentum a u) p 0 := by
  have near : pi =ᶠ[𝓝 p] actualScalarCanonicalMomentum a u := by
    filter_upwards [D.isOpen.mem_nhds inside] with q hq
    exact same hq
  exact congrArg (fun L : CoordinatePoint →L[ℝ] ℝ => L (Pi.single 0 1)) near.fderiv_eq

theorem independent_hamilton_pair_iff_same_kg (a : Parameters) (u pi : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ (⊤ : ℕ∞) u) (D : Opens CoordinatePoint) :
    ScalarHamiltonPairOn a u pi D ↔
      EqOn pi (actualScalarCanonicalMomentum a u) D ∧
        ∀ p ∈ D, scalarFieldWaveOperator (sourceMetric a) u p = massWaveNumber a ^ 2 * u p := by
  constructor
  · rintro ⟨first, second⟩
    have same : EqOn pi (actualScalarCanonicalMomentum a u) D := by
      intro p inside
      have equation := first p inside
      change pi p = sourceFactor a p * scalarPartial u p 0
      field_simp [source_factor_nonzero a p] at equation
      linarith
    refine ⟨same, ?_⟩
    intro p inside
    apply (scalar_hamilton_equations_iff_same_kg a u p
      (regular.contDiffAt.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))).mp
    refine ⟨actual_scalar_first_hamilton_equation a u p, ?_⟩
    rw [← scalar_momentum_derivative_local a u pi D same p inside]
    exact second p inside
  · rintro ⟨same, equation⟩
    constructor
    · intro p inside
      rw [same inside]
      simp [actualScalarCanonicalMomentum, scalarCanonicalMomentum, source_factor_nonzero a p]
    · intro p inside
      rw [scalar_momentum_derivative_local a u pi D same p inside]
      exact ((scalar_hamilton_equations_iff_same_kg a u p
        (regular.contDiffAt.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))).mpr
          (equation p inside)).2

end AASCKleinGordon.SameActionSource
