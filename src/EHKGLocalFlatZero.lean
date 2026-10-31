import EHKGLocalFlatUniqueness
import EHKGTimeReflection
import EHKGScalarLinearPDE

/-! Both time directions and uniqueness among arbitrary locally smooth
solutions on the diamond. No Schwartz or global homogeneous-PDE assumption. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

theorem local_flat_zero (nu mu : ℝ) (mass : mu ≠ 0) (F : CoordinatePoint → ℝ)
    (regular : ContDiffOn ℝ (⊤ : ℕ∞) F (protectedDiamond nu))
    (equation : ∀ q ∈ protectedDiamond nu, flatScalarResidual (mu ^ 2) F q = 0)
    (position : ∀ x ∈ centralLeafDomain nu, F (centralLeafPoint x) = 0)
    (velocity : ∀ x ∈ centralLeafDomain nu, scalarPartial F (centralLeafPoint x) 0 = 0)
    (p : CoordinatePoint) (inside : p ∈ protectedDiamond nu) : F p = 0 := by
  by_cases future : 0 ≤ p 0
  · exact local_flat_future_zero nu mu mass F regular equation position velocity p inside future
  · have reflectedRegular : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => F (timeReflectionCLM x)) (protectedDiamond nu) :=
      regular.comp timeReflectionCLM.contDiff.contDiffOn (fun q hq => (time_reflection_diamond nu q).mpr hq)
    have reflectedEquation (q : CoordinatePoint) (hq : q ∈ protectedDiamond nu) :
        flatScalarResidual (mu ^ 2) (fun x => F (timeReflectionCLM x)) q = 0 := by
      have reflectedInside := (time_reflection_diamond nu q).mpr hq
      have regularAt := regular.contDiffAt ((protected_diamond_open nu).mem_nhds reflectedInside)
      rw [flat_residual_time_reflection _ F q
        (regularAt.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))]
      exact equation _ reflectedInside
    have reflectedPosition (x : KGSpatialSpace) (hx : x ∈ centralLeafDomain nu) :
        F (timeReflectionCLM (centralLeafPoint x)) = 0 := by rw [time_reflection_central]; exact position x hx
    have reflectedVelocity (x : KGSpatialSpace) (hx : x ∈ centralLeafDomain nu) :
        scalarPartial (fun q => F (timeReflectionCLM q)) (centralLeafPoint x) 0 = 0 := by
      have regularAt : DifferentiableAt ℝ F (timeReflectionCLM (centralLeafPoint x)) := by
        rw [time_reflection_central]
        exact (regular.contDiffAt ((protected_diamond_open nu).mem_nhds
          ((central_leaf_in_diamond_iff nu x).mpr hx))).differentiableAt (by simp)
      rw [scalar_time_partial_time_reflection F _ regularAt, time_reflection_central, velocity x hx, neg_zero]
    have reflectedInside := (time_reflection_diamond nu p).mpr inside
    have reflectedFuture : 0 ≤ timeReflectionCLM p 0 := by rw [time_reflection_time]; linarith
    have zero := local_flat_future_zero nu mu mass (fun x => F (timeReflectionCLM x)) reflectedRegular
      reflectedEquation reflectedPosition reflectedVelocity (timeReflectionCLM p) reflectedInside reflectedFuture
    simpa only [time_reflection_involutive] using zero

theorem local_flat_unique (nu mu : ℝ) (mass : mu ≠ 0) (F G : CoordinatePoint → ℝ)
    (regularF : ContDiffOn ℝ (⊤ : ℕ∞) F (protectedDiamond nu))
    (regularG : ContDiffOn ℝ (⊤ : ℕ∞) G (protectedDiamond nu))
    (equationF : ∀ q ∈ protectedDiamond nu, flatScalarResidual (mu ^ 2) F q = 0)
    (equationG : ∀ q ∈ protectedDiamond nu, flatScalarResidual (mu ^ 2) G q = 0)
    (position : ∀ x ∈ centralLeafDomain nu, F (centralLeafPoint x) = G (centralLeafPoint x))
    (velocity : ∀ x ∈ centralLeafDomain nu, scalarPartial F (centralLeafPoint x) 0 = scalarPartial G (centralLeafPoint x) 0)
    (p : CoordinatePoint) (inside : p ∈ protectedDiamond nu) : F p = G p := by
  apply sub_eq_zero.mp
  apply local_flat_zero nu mu mass (fun x => F x - G x) (regularF.sub regularG)
  · intro q hq
    have atF := regularF.contDiffAt ((protected_diamond_open nu).mem_nhds hq)
    have atG := regularG.contDiffAt ((protected_diamond_open nu).mem_nhds hq)
    rw [flat_residual_sub_local _ F G q
      (atF.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
      (atG.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))), equationF q hq, equationG q hq, sub_self]
  · intro x hx
    exact sub_eq_zero.mpr (position x hx)
  · intro x hx
    have inD := (central_leaf_in_diamond_iff nu x).mpr hx
    have atF := (regularF.contDiffAt ((protected_diamond_open nu).mem_nhds inD)).differentiableAt (by simp)
    have atG := (regularG.contDiffAt ((protected_diamond_open nu).mem_nhds inD)).differentiableAt (by simp)
    rw [scalar_partial_sub_local F G _ atF atG, velocity x hx, sub_self]
  · exact inside

end AASCKleinGordon.CurvedKG
