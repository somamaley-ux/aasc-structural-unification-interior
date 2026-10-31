import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add

noncomputable section
set_option maxHeartbeats 600000
namespace AASCKleinGordon

abbrev KGSpatialSpace := EuclideanSpace ℝ (Fin 3)

/-- Real Klein–Gordon energy, in the spatial Euclidean norm and coordinate τ=x⁰. -/
def flatKGEnergy (μ u v : ℝ) (w : KGSpatialSpace) : ℝ :=
  (v^2+‖w‖^2+μ^2*u^2)/2

def flatKGFlux (v : ℝ) (w : KGSpatialSpace) : KGSpatialSpace := v • w

theorem flatKGEnergy_nonneg (μ u v : ℝ) (w : KGSpatialSpace) :
    0 ≤ flatKGEnergy μ u v w := by
  unfold flatKGEnergy
  positivity

theorem flatKGFlux_norm_le_energy (μ u v : ℝ) (w : KGSpatialSpace) :
    ‖flatKGFlux v w‖ ≤ flatKGEnergy μ u v w := by
  rw [flatKGFlux,norm_smul,Real.norm_eq_abs]
  unfold flatKGEnergy
  nlinarith [sq_nonneg (|v|-‖w‖),sq_abs v,mul_nonneg (sq_nonneg μ) (sq_nonneg u)]

theorem flatKGFlux_inner_le (μ u v : ℝ) (w ξ : KGSpatialSpace) :
    |inner ℝ ξ (flatKGFlux v w)| ≤ ‖ξ‖*flatKGEnergy μ u v w :=
  (abs_real_inner_le_norm ξ (flatKGFlux v w)).trans
    (mul_le_mul_of_nonneg_left (flatKGFlux_norm_le_energy μ u v w) (norm_nonneg ξ))

theorem flatKGEnergy_eq_zero_iff (μ u v : ℝ) (w : KGSpatialSpace) (hμ : μ ≠ 0) :
    flatKGEnergy μ u v w = 0 ↔ u=0 ∧ v=0 ∧ w=0 := by
  constructor
  · intro h
    have hm : 0 < μ^2 := sq_pos_of_ne_zero hμ
    have hu : μ^2*u^2=0 := by
      unfold flatKGEnergy at h
      nlinarith [sq_nonneg v,sq_nonneg ‖w‖,mul_nonneg (sq_nonneg μ) (sq_nonneg u)]
    have hv : v=0 := by
      unfold flatKGEnergy at h
      nlinarith [sq_nonneg ‖w‖,mul_nonneg (sq_nonneg μ) (sq_nonneg u)]
    have hw : ‖w‖=0 := by
      unfold flatKGEnergy at h
      nlinarith [sq_nonneg v,mul_nonneg (sq_nonneg μ) (sq_nonneg u)]
    exact ⟨sq_eq_zero_iff.mp ((mul_eq_zero.mp hu).resolve_left (ne_of_gt hm)),hv,norm_eq_zero.mp hw⟩
  · rintro ⟨rfl,rfl,rfl⟩
    simp [flatKGEnergy]

/-- Pointwise balance from the actual first-order KG derivative identities.
`d` is spatial divergence of `w`; `g` is the spatial gradient of `v`.
The spatial integration-by-parts theorem supplies their later integral interpretation. -/
theorem flatKGEnergy_hasDerivAt
    (μ : ℝ) (u v : ℝ → ℝ) (w : ℝ → KGSpatialSpace)
    (t d : ℝ) (g : KGSpatialSpace)
    (hu : HasDerivAt u (v t) t)
    (hv : HasDerivAt v (d-μ^2*u t) t)
    (hw : HasDerivAt w g t) :
    HasDerivAt (fun s => flatKGEnergy μ (u s) (v s) (w s))
      (v t*d+inner ℝ (w t) g) t := by
  convert (((hv.pow 2).add hw.norm_sq).add ((hu.pow 2).const_mul (μ^2))).div_const 2 using 1 <;>
    simp only [flatKGEnergy,pow_one,Nat.cast_ofNat]
  <;> ring

/-- The sign needed after spatial integration by parts. -/
theorem flatKG_weighted_energy_rate_nonpos
    (μ u v χt : ℝ) (w ξ : KGSpatialSpace)
    (hcut : χt+‖ξ‖ ≤ 0) :
    χt*flatKGEnergy μ u v w-inner ℝ ξ (flatKGFlux v w) ≤ 0 := by
  have hflux := flatKGFlux_inner_le μ u v w ξ
  have he := flatKGEnergy_nonneg μ u v w
  have hi := neg_abs_le (inner ℝ ξ (flatKGFlux v w))
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hcut he]

end AASCKleinGordon
