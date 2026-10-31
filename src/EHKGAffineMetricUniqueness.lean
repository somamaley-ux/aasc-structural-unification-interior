import EHKGAffineDiamondUniqueness
import EHKGShiftedCauchyConstruction
import EHKGSameMetricUniqueness

/-! Same-EH metric uniqueness on contained shifted dependence diamonds.
Both traces refer to the actual field and geometric unit normal. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

theorem secant_lift_regular_on (nu : ℝ) (D : Set CoordinatePoint)
    (inside : D ⊆ protectedDiamond nu) (u : CoordinatePoint → ℝ)
    (regular : ContDiffOn ℝ (⊤ : ℕ∞) u D) : ContDiffOn ℝ (⊤ : ℕ∞) (secantLift nu u) D := by
  have cosine : ContDiff ℝ (⊤ : ℕ∞) (fun p : CoordinatePoint => Real.cos (nu * p 0)) := by fun_prop
  have scale : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : CoordinatePoint => secantScale nu (p 0)) D :=
    cosine.contDiffOn.inv (fun p hp => ne_of_gt (protected_cosine_positive nu p (protected_diamond_subset_ball nu (inside hp))))
  exact scale.mul regular

theorem secant_lift_flat_equation_on (a : Parameters) (D : Set CoordinatePoint) (opened : IsOpen D)
    (inside : D ⊆ protectedDiamond (conformalFrequency a)) (u : CoordinatePoint → ℝ)
    (regular : ContDiffOn ℝ (⊤ : ℕ∞) u D)
    (equation : ∀ p ∈ D,
      scalarFieldWaveOperator (originalEHActMetric (conformalOperand (conformalFrequency a))) u p =
        (massWaveNumber a) ^ 2 * u p) (p : CoordinatePoint) (hp : p ∈ D) :
    flatScalarResidual ((conformalFrequency a) ^ 2) (secantLift (conformalFrequency a) u) p = 0 := by
  have atU := regular.contDiffAt (opened.mem_nhds hp)
  have conjugacy := protected_same_eh_conjugacy a p (protected_diamond_subset_ball _ (inside hp)) u
    (atU.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
  rw [auxiliary_mass_wave_number, equation p hp, sub_self, mul_zero] at conjugacy
  exact conjugacy

theorem secant_lift_trace_time (nu : ℝ) (u v : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (safe : Real.cos (nu * p 0) ≠ 0) (regularU : DifferentiableAt ℝ u p) (regularV : DifferentiableAt ℝ v p)
    (position : u p = v p) (normal : actualNormalDerivative nu u p = actualNormalDerivative nu v p) :
    scalarPartial (secantLift nu u) p 0 = scalarPartial (secantLift nu v) p 0 := by
  have velocity : scalarPartial u p 0 = scalarPartial v p 0 := by
    rw [normal_derivative_is_cosine_partial, normal_derivative_is_cosine_partial] at normal
    exact mul_left_cancel₀ safe normal
  have scale := (secant_scale_hasDerivAt nu (p 0) safe).comp_hasFDerivAt p
    (ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ).hasFDerivAt
  have derivU := (scale.mul regularU.hasFDerivAt).fderiv
  have derivV := (scale.mul regularV.hasFDerivAt).fderiv
  change fderiv ℝ (fun q => secantScale nu (q 0) * u q) p = _ at derivU
  change fderiv ℝ (fun q => secantScale nu (q 0) * v q) p = _ at derivV
  change fderiv ℝ (fun q => secantScale nu (q 0) * u q) p (Pi.single 0 1) =
    fderiv ℝ (fun q => secantScale nu (q 0) * v q) p (Pi.single 0 1)
  rw [derivU, derivV]
  change secantScale nu (p 0) * scalarPartial u p 0 + u p * _ =
    secantScale nu (p 0) * scalarPartial v p 0 + v p * _
  rw [velocity, position]

theorem affine_same_eh_local_unique (a : Parameters) (time scale : ℝ) (scaleNonzero : scale ≠ 0)
    (inside : affineDependenceDiamond (conformalFrequency a) time scale ⊆ protectedDiamond (conformalFrequency a))
    (u v : CoordinatePoint → ℝ)
    (regularU : ContDiffOn ℝ (⊤ : ℕ∞) u (affineDependenceDiamond (conformalFrequency a) time scale))
    (regularV : ContDiffOn ℝ (⊤ : ℕ∞) v (affineDependenceDiamond (conformalFrequency a) time scale))
    (equationU : ∀ p ∈ affineDependenceDiamond (conformalFrequency a) time scale,
      scalarFieldWaveOperator (originalEHActMetric (conformalOperand (conformalFrequency a))) u p = (massWaveNumber a) ^ 2 * u p)
    (equationV : ∀ p ∈ affineDependenceDiamond (conformalFrequency a) time scale,
      scalarFieldWaveOperator (originalEHActMetric (conformalOperand (conformalFrequency a))) v p = (massWaveNumber a) ^ 2 * v p)
    (position : ∀ x ∈ centralLeafDomain (conformalFrequency a), u (affineCauchyPoint time scale x) = v (affineCauchyPoint time scale x))
    (normal : ∀ x ∈ centralLeafDomain (conformalFrequency a),
      actualNormalDerivative (conformalFrequency a) u (affineCauchyPoint time scale x) =
        actualNormalDerivative (conformalFrequency a) v (affineCauchyPoint time scale x))
    (p : CoordinatePoint) (hp : p ∈ affineDependenceDiamond (conformalFrequency a) time scale) : u p = v p := by
  let D := affineDependenceDiamond (conformalFrequency a) time scale
  have opened := affine_diamond_open (conformalFrequency a) time scale
  have velocity (x : KGSpatialSpace) (hx : x ∈ centralLeafDomain (conformalFrequency a)) :
      scalarPartial (secantLift (conformalFrequency a) u) (affineCauchyPoint time scale x) 0 =
        scalarPartial (secantLift (conformalFrequency a) v) (affineCauchyPoint time scale x) 0 := by
    have pointInside := affine_cauchy_point_inside (conformalFrequency a) time scale scaleNonzero x hx
    exact secant_lift_trace_time _ u v _
      (ne_of_gt (protected_cosine_positive _ _ (protected_diamond_subset_ball _ (inside pointInside))))
      ((regularU.contDiffAt (opened.mem_nhds pointInside)).differentiableAt (by simp))
      ((regularV.contDiffAt (opened.mem_nhds pointInside)).differentiableAt (by simp)) (position x hx) (normal x hx)
  have lifted := affine_local_flat_unique (conformalFrequency a) time scale (conformalFrequency a)
    scaleNonzero (ne_of_gt (conformal_frequency_positive a)) (secantLift (conformalFrequency a) u)
    (secantLift (conformalFrequency a) v)
    (secant_lift_regular_on _ D inside u regularU) (secant_lift_regular_on _ D inside v regularV)
    (secant_lift_flat_equation_on a D opened inside u regularU equationU)
    (secant_lift_flat_equation_on a D opened inside v regularV equationV)
    (fun x hx => by dsimp only [secantLift]; rw [position x hx]) velocity p hp
  exact mul_left_cancel₀ (inv_ne_zero (ne_of_gt
    (protected_cosine_positive _ p (protected_diamond_subset_ball _ (inside hp))))) lifted

end AASCKleinGordon.CurvedKG
