import EHKGFixedMassFlatSpecialization
import EHKGLocalFlatZero

/-! Bounded uniqueness-based reception of the actual H=0 Cauchy family at
the original positive physical mass. This is not a limit of the mass-tuned
curved branch and is not quantitative SR/nonrelativistic recovery. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

theorem fixed_mass_flat_local_cauchy_unique (a : Parameters)
    (f h : TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞))
    (v : CoordinatePoint → ℝ)
    (regular : ContDiffOn ℝ (⊤ : ℕ∞) v (protectedDiamond (conformalFrequency a)))
    (equation : ∀ p ∈ protectedDiamond (conformalFrequency a),
      scalarFieldWaveOperator (originalEHActMetric (0 : MetricSourceProbe (⊤ : Opens CoordinatePoint))) v p =
        (massWaveNumber a) ^ 2 * v p)
    (position : ∀ x ∈ centralLeafDomain (conformalFrequency a), v (centralLeafPoint x) = f x)
    (velocity : ∀ x ∈ centralLeafDomain (conformalFrequency a), scalarPartial v (centralLeafPoint x) 0 = h x) :
    EqOn v (compactFlatField a (centralLeafDomain (conformalFrequency a)) f h) (protectedDiamond (conformalFrequency a)) := by
  have flatEquation (p : CoordinatePoint) (hp : p ∈ protectedDiamond (conformalFrequency a)) :
      flatScalarResidual ((massWaveNumber a) ^ 2) v p = 0 := by
    have identity := zero_eh_operator_is_original_flat ((massWaveNumber a) ^ 2) v p
    rw [equation p hp, sub_self] at identity
    linarith
  intro p hp
  have massPositive : 0 < massWaveNumber a := by
    have hm := a.mass_pos
    have hc := a.speed_pos
    have hh := a.hbar_pos
    dsimp [massWaveNumber]
    positivity
  exact local_flat_unique (conformalFrequency a) (massWaveNumber a) (ne_of_gt massPositive)
    v (compactFlatField a (centralLeafDomain (conformalFrequency a)) f h) regular
    (fixed_mass_flat_field_smooth a _ f h).contDiffOn flatEquation
    (fun q _ => flat_coordinate_residual_zero a _ _ Complex.reCLM q)
    (fun x hx => (position x hx).trans (fixed_mass_flat_initial_position a _ f h x).symm)
    (fun x hx => (velocity x hx).trans (fixed_mass_flat_initial_velocity a _ f h x).symm) p hp

end AASCKleinGordon.CurvedKG
