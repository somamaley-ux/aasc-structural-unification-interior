import EHKGLocalFlatZero

/-! Transport actual local smooth uniqueness to the same admitted original
EH metric. Initial velocity is the proved geometric normal derivative. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

def secantLift (nu : ℝ) (u : CoordinatePoint → ℝ) (p : CoordinatePoint) : ℝ :=
  secantScale nu (p 0) * u p

theorem secant_lift_regular (nu : ℝ) (u : CoordinatePoint → ℝ)
    (regular : ContDiffOn ℝ (⊤ : ℕ∞) u (protectedDiamond nu)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (secantLift nu u) (protectedDiamond nu) := by
  have cosine : ContDiff ℝ (⊤ : ℕ∞) (fun p : CoordinatePoint => Real.cos (nu * p 0)) := by fun_prop
  have scale : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : CoordinatePoint => secantScale nu (p 0)) (protectedDiamond nu) :=
    cosine.contDiffOn.inv (fun p hp => ne_of_gt (protected_cosine_positive nu p (protected_diamond_subset_ball nu hp)))
  exact scale.mul regular

theorem secant_lift_flat_equation (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiffOn ℝ (⊤ : ℕ∞) u (protectedDiamond (conformalFrequency a)))
    (equation : ∀ p ∈ protectedDiamond (conformalFrequency a),
      scalarFieldWaveOperator (originalEHActMetric (conformalOperand (conformalFrequency a))) u p =
        (massWaveNumber a) ^ 2 * u p) (p : CoordinatePoint) (inside : p ∈ protectedDiamond (conformalFrequency a)) :
    flatScalarResidual ((conformalFrequency a) ^ 2) (secantLift (conformalFrequency a) u) p = 0 := by
  have regularAt := regular.contDiffAt ((protected_diamond_open _).mem_nhds inside)
  have conjugacy := protected_same_eh_conjugacy a p (protected_diamond_subset_ball _ inside) u
    (regularAt.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
  rw [auxiliary_mass_wave_number, equation p inside, sub_self, mul_zero] at conjugacy
  exact conjugacy

theorem secant_lift_initial_position (nu : ℝ) (u : CoordinatePoint → ℝ) (x : KGSpatialSpace) :
    secantLift nu u (centralLeafPoint x) = u (centralLeafPoint x) := by
  simp only [secantLift, central_leaf_time, secant_scale_zero, one_mul]

theorem secant_lift_initial_time (nu : ℝ) (u : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (initialTime : p 0 = 0) (regular : DifferentiableAt ℝ u p) :
    scalarPartial (secantLift nu u) p 0 = scalarPartial u p 0 := by
  have scale := (secant_scale_hasDerivAt nu (p 0) (by simp [initialTime])).comp_hasFDerivAt p
    (ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ).hasFDerivAt
  have scaleZero : HasFDerivAt (fun x : CoordinatePoint => secantScale nu (x 0))
      (0 : CoordinatePoint →L[ℝ] ℝ) p := by
    simpa only [initialTime, secant_velocity_zero, zero_smul] using scale
  have productDerivative := (scaleZero.mul regular.hasFDerivAt).fderiv
  change fderiv ℝ (fun x => secantScale nu (x 0) * u x) p = _ at productDerivative
  change fderiv ℝ (fun x => secantScale nu (x 0) * u x) p (Pi.single 0 1) = _
  rw [productDerivative]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply,
    smul_eq_mul, initialTime, secant_scale_zero, one_mul, mul_zero, add_zero, scalarPartial]

theorem same_eh_local_smooth_unique (a : Parameters) (u v : CoordinatePoint → ℝ)
    (regularU : ContDiffOn ℝ (⊤ : ℕ∞) u (protectedDiamond (conformalFrequency a)))
    (regularV : ContDiffOn ℝ (⊤ : ℕ∞) v (protectedDiamond (conformalFrequency a)))
    (equationU : ∀ p ∈ protectedDiamond (conformalFrequency a),
      scalarFieldWaveOperator (originalEHActMetric (conformalOperand (conformalFrequency a))) u p =
        (massWaveNumber a) ^ 2 * u p)
    (equationV : ∀ p ∈ protectedDiamond (conformalFrequency a),
      scalarFieldWaveOperator (originalEHActMetric (conformalOperand (conformalFrequency a))) v p =
        (massWaveNumber a) ^ 2 * v p)
    (position : ∀ x ∈ centralLeafDomain (conformalFrequency a), u (centralLeafPoint x) = v (centralLeafPoint x))
    (normal : ∀ x ∈ centralLeafDomain (conformalFrequency a),
      actualNormalDerivative (conformalFrequency a) u (centralLeafPoint x) =
        actualNormalDerivative (conformalFrequency a) v (centralLeafPoint x))
    (p : CoordinatePoint) (inside : p ∈ protectedDiamond (conformalFrequency a)) : u p = v p := by
  have velocity (x : KGSpatialSpace) (hx : x ∈ centralLeafDomain (conformalFrequency a)) :
      scalarPartial (secantLift (conformalFrequency a) u) (centralLeafPoint x) 0 =
        scalarPartial (secantLift (conformalFrequency a) v) (centralLeafPoint x) 0 := by
    have inD := (central_leaf_in_diamond_iff _ x).mpr hx
    have atU := (regularU.contDiffAt ((protected_diamond_open _).mem_nhds inD)).differentiableAt (by simp)
    have atV := (regularV.contDiffAt ((protected_diamond_open _).mem_nhds inD)).differentiableAt (by simp)
    rw [secant_lift_initial_time _ u _ (central_leaf_time x) atU,
      secant_lift_initial_time _ v _ (central_leaf_time x) atV]
    have equal := normal x hx
    rw [actualNormalDerivative, actualNormalDerivative, central_normal_is_coordinate] at equal
    exact equal
  have lifted := local_flat_unique (conformalFrequency a) (conformalFrequency a)
    (ne_of_gt (conformal_frequency_positive a)) (secantLift (conformalFrequency a) u)
    (secantLift (conformalFrequency a) v) (secant_lift_regular _ u regularU) (secant_lift_regular _ v regularV)
    (secant_lift_flat_equation a u regularU equationU) (secant_lift_flat_equation a v regularV equationV)
    (fun x hx => by rw [secant_lift_initial_position, secant_lift_initial_position]; exact position x hx) velocity p inside
  have nonzero : secantScale (conformalFrequency a) (p 0) ≠ 0 :=
    ne_of_gt (secant_scale_positive _ _ (protected_cosine_positive _ p (protected_diamond_subset_ball _ inside)))
  exact mul_left_cancel₀ nonzero lifted

end AASCKleinGordon.CurvedKG
