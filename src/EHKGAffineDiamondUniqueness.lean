import EHKGTimeAffineCalculus
import EHKGCoordinateFoliation

/-! Actual translated/rescaled dependence diamonds. Uniqueness transfers
from the proved local energy theorem through an invertible affine map;
its initial surface is the shifted diamond's own central leaf. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

theorem time_affine_coordinate (time scale : ℝ) (p : CoordinatePoint) (c : Fin 4) :
    timeAffineMap time scale p c = time * (Pi.single (0 : Fin 4) (1 : ℝ) : CoordinatePoint) c + scale * p c := rfl

theorem time_affine_inverse_left (time scale : ℝ) (nonzero : scale ≠ 0) (p : CoordinatePoint) :
    timeAffineMap (-time / scale) scale⁻¹ (timeAffineMap time scale p) = p := by
  funext c
  simp only [time_affine_coordinate]
  field_simp
  <;> ring

theorem time_affine_inverse_right (time scale : ℝ) (nonzero : scale ≠ 0) (p : CoordinatePoint) :
    timeAffineMap time scale (timeAffineMap (-time / scale) scale⁻¹ p) = p := by
  funext c
  simp only [time_affine_coordinate]
  field_simp
  <;> ring

def affineDependenceDiamond (nu time scale : ℝ) : Set CoordinatePoint :=
  (timeAffineMap (-time / scale) scale⁻¹) ⁻¹' protectedDiamond nu

theorem affine_diamond_open (nu time scale : ℝ) : IsOpen (affineDependenceDiamond nu time scale) :=
  (protected_diamond_open nu).preimage (time_affine_smooth _ _).continuous

theorem affine_diamond_image (nu time scale : ℝ) (nonzero : scale ≠ 0) (p : CoordinatePoint) :
    timeAffineMap time scale p ∈ affineDependenceDiamond nu time scale ↔ p ∈ protectedDiamond nu := by
  change timeAffineMap (-time / scale) scale⁻¹ (timeAffineMap time scale p) ∈ protectedDiamond nu ↔ _
  rw [time_affine_inverse_left time scale nonzero]

def affineCauchyPoint (time scale : ℝ) (x : KGSpatialSpace) : CoordinatePoint :=
  timeAffineMap time scale (centralLeafPoint x)

theorem affine_cauchy_point_inside (nu time scale : ℝ) (nonzero : scale ≠ 0)
    (x : KGSpatialSpace) (inside : x ∈ centralLeafDomain nu) :
    affineCauchyPoint time scale x ∈ affineDependenceDiamond nu time scale :=
  (affine_diamond_image nu time scale nonzero _).mpr ((central_leaf_in_diamond_iff nu x).mpr inside)

theorem affine_local_flat_zero (nu time scale mu : ℝ) (scaleNonzero : scale ≠ 0) (mass : mu ≠ 0)
    (F : CoordinatePoint → ℝ)
    (regular : ContDiffOn ℝ (⊤ : ℕ∞) F (affineDependenceDiamond nu time scale))
    (equation : ∀ q ∈ affineDependenceDiamond nu time scale, flatScalarResidual (mu ^ 2) F q = 0)
    (position : ∀ x ∈ centralLeafDomain nu, F (affineCauchyPoint time scale x) = 0)
    (velocity : ∀ x ∈ centralLeafDomain nu, scalarPartial F (affineCauchyPoint time scale x) 0 = 0)
    (p : CoordinatePoint) (inside : p ∈ affineDependenceDiamond nu time scale) : F p = 0 := by
  have maps : MapsTo (timeAffineMap time scale) (protectedDiamond nu) (affineDependenceDiamond nu time scale) :=
    fun q hq => (affine_diamond_image nu time scale scaleNonzero q).mpr hq
  have pullRegular : ContDiffOn ℝ (⊤ : ℕ∞) (fun q => F (timeAffineMap time scale q)) (protectedDiamond nu) :=
    regular.comp (time_affine_smooth time scale).contDiffOn maps
  have pullEquation (q : CoordinatePoint) (hq : q ∈ protectedDiamond nu) :
      flatScalarResidual ((scale * mu) ^ 2) (fun x => F (timeAffineMap time scale x)) q = 0 := by
    have atF := regular.contDiffAt ((affine_diamond_open nu time scale).mem_nhds (maps hq))
    rw [flat_residual_time_affine time scale mu F q
      (atF.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))), equation _ (maps hq), mul_zero]
  have pullVelocity (x : KGSpatialSpace) (hx : x ∈ centralLeafDomain nu) :
      scalarPartial (fun q => F (timeAffineMap time scale q)) (centralLeafPoint x) 0 = 0 := by
    have atF := (regular.contDiffAt ((affine_diamond_open nu time scale).mem_nhds
      (affine_cauchy_point_inside nu time scale scaleNonzero x hx))).differentiableAt (by simp)
    rw [scalar_partial_time_affine time scale F _ atF]
    change scale * scalarPartial F (affineCauchyPoint time scale x) 0 = 0
    rw [velocity x hx, mul_zero]
  have zero := local_flat_zero nu (scale * mu) (mul_ne_zero scaleNonzero mass)
    (fun q => F (timeAffineMap time scale q)) pullRegular pullEquation position pullVelocity
    (timeAffineMap (-time / scale) scale⁻¹ p) inside
  simpa only [time_affine_inverse_right time scale scaleNonzero] using zero

theorem affine_local_flat_unique (nu time scale mu : ℝ) (scaleNonzero : scale ≠ 0) (mass : mu ≠ 0)
    (F G : CoordinatePoint → ℝ)
    (regularF : ContDiffOn ℝ (⊤ : ℕ∞) F (affineDependenceDiamond nu time scale))
    (regularG : ContDiffOn ℝ (⊤ : ℕ∞) G (affineDependenceDiamond nu time scale))
    (equationF : ∀ q ∈ affineDependenceDiamond nu time scale, flatScalarResidual (mu ^ 2) F q = 0)
    (equationG : ∀ q ∈ affineDependenceDiamond nu time scale, flatScalarResidual (mu ^ 2) G q = 0)
    (position : ∀ x ∈ centralLeafDomain nu, F (affineCauchyPoint time scale x) = G (affineCauchyPoint time scale x))
    (velocity : ∀ x ∈ centralLeafDomain nu,
      scalarPartial F (affineCauchyPoint time scale x) 0 = scalarPartial G (affineCauchyPoint time scale x) 0)
    (p : CoordinatePoint) (inside : p ∈ affineDependenceDiamond nu time scale) : F p = G p := by
  apply sub_eq_zero.mp
  apply affine_local_flat_zero nu time scale mu scaleNonzero mass (fun q => F q - G q) (regularF.sub regularG)
  · intro q hq
    have atF := regularF.contDiffAt ((affine_diamond_open nu time scale).mem_nhds hq)
    have atG := regularG.contDiffAt ((affine_diamond_open nu time scale).mem_nhds hq)
    rw [flat_residual_sub_local _ F G q
      (atF.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
      (atG.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))), equationF q hq, equationG q hq, sub_self]
  · intro x hx; exact sub_eq_zero.mpr (position x hx)
  · intro x hx
    have pointInside := affine_cauchy_point_inside nu time scale scaleNonzero x hx
    have atF := (regularF.contDiffAt ((affine_diamond_open nu time scale).mem_nhds pointInside)).differentiableAt (by simp)
    have atG := (regularG.contDiffAt ((affine_diamond_open nu time scale).mem_nhds pointInside)).differentiableAt (by simp)
    rw [scalar_partial_sub_local F G _ atF atG, velocity x hx, sub_self]
  · exact inside

end AASCKleinGordon.CurvedKG
