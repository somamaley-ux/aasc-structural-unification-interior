import KGFlatEnergyAlgebra
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.ProperSpace.Real

noncomputable section
set_option maxHeartbeats 600000
open scoped Topology
namespace AASCKleinGordon

def regularizedSpatialDistance (δ : ℝ) (x₀ x : KGSpatialSpace) : ℝ :=
  Real.sqrt (δ^2+‖x-x₀‖^2)

def regularizedDistanceGradient (δ : ℝ) (x₀ x : KGSpatialSpace) : KGSpatialSpace :=
  (regularizedSpatialDistance δ x₀ x)⁻¹ • (x-x₀)

theorem regularizedSpatialDistance_pos (δ : ℝ) (x₀ x : KGSpatialSpace) (hδ : 0 < δ) :
    0 < regularizedSpatialDistance δ x₀ x := by
  apply Real.sqrt_pos.2
  nlinarith [sq_pos_of_pos hδ,sq_nonneg ‖x-x₀‖]

theorem norm_sub_le_regularizedDistance (δ : ℝ) (x₀ x : KGSpatialSpace) :
    ‖x-x₀‖ ≤ regularizedSpatialDistance δ x₀ x := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ δ^2+‖x-x₀‖^2)
  have hp := Real.sqrt_nonneg (δ^2+‖x-x₀‖^2)
  unfold regularizedSpatialDistance
  nlinarith [sq_nonneg δ,norm_nonneg (x-x₀)]

theorem regularizedDistanceGradient_norm_le_one
    (δ : ℝ) (x₀ x : KGSpatialSpace) (hδ : 0 < δ) :
    ‖regularizedDistanceGradient δ x₀ x‖ ≤ 1 := by
  have hp := regularizedSpatialDistance_pos δ x₀ x hδ
  rw [regularizedDistanceGradient,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.2 hp)]
  rw [← div_eq_inv_mul]
  exact (div_le_one hp).2 (norm_sub_le_regularizedDistance δ x₀ x)

theorem regularizedSpatialDistance_hasFDerivAt
    (δ : ℝ) (x₀ x : KGSpatialSpace) (hδ : 0 < δ) :
    HasFDerivAt (regularizedSpatialDistance δ x₀)
      (innerSL ℝ (regularizedDistanceGradient δ x₀ x)) x := by
  have hr : δ^2+‖x-x₀‖^2 ≠ 0 := by
    have := sq_pos_of_pos hδ
    positivity
  have hf := (((hasFDerivAt_id x).sub_const x₀).norm_sq.const_add (δ^2)).sqrt hr
  convert hf using 1
  ext z
  simp [regularizedDistanceGradient,regularizedSpatialDistance,smul_smul]
  <;> ring

theorem regularizedSpatialDistance_contDiff (δ : ℝ) (x₀ : KGSpatialSpace) (hδ : 0 < δ) :
    ContDiff ℝ 2 (regularizedSpatialDistance δ x₀) := by
  apply (contDiff_const.add ((contDiff_id.sub contDiff_const).norm_sq ℝ)).sqrt
  intro x
  have := sq_pos_of_pos hδ
  positivity

def smoothConeCutoff (δ R t : ℝ) (x₀ x : KGSpatialSpace) : ℝ :=
  Real.smoothTransition (R-t-regularizedSpatialDistance δ x₀ x)

def smoothConeCutoffTimeDerivative (δ R t : ℝ) (x₀ x : KGSpatialSpace) : ℝ :=
  -deriv Real.smoothTransition (R-t-regularizedSpatialDistance δ x₀ x)

def smoothConeCutoffGradient (δ R t : ℝ) (x₀ x : KGSpatialSpace) : KGSpatialSpace :=
  smoothConeCutoffTimeDerivative δ R t x₀ x • regularizedDistanceGradient δ x₀ x

theorem smoothConeCutoff_nonneg (δ R t : ℝ) (x₀ x : KGSpatialSpace) :
    0 ≤ smoothConeCutoff δ R t x₀ x := Real.smoothTransition.nonneg _

theorem smoothConeCutoff_hasDerivAt (δ R t : ℝ) (x₀ x : KGSpatialSpace) :
    HasDerivAt (fun s => smoothConeCutoff δ R s x₀ x)
      (smoothConeCutoffTimeDerivative δ R t x₀ x) t := by
  have he : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
  convert (he (R-t-regularizedSpatialDistance δ x₀ x)).hasDerivAt.comp t
    (((hasDerivAt_const t R).sub (hasDerivAt_id t)).sub_const
      (regularizedSpatialDistance δ x₀ x)) using 1 <;>
    simp [smoothConeCutoff,smoothConeCutoffTimeDerivative]

theorem smoothConeCutoff_hasFDerivAt
    (δ R t : ℝ) (x₀ x : KGSpatialSpace) (hδ : 0 < δ) :
    HasFDerivAt (smoothConeCutoff δ R t x₀)
      (innerSL ℝ (smoothConeCutoffGradient δ R t x₀ x)) x := by
  have he : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
  have hf := (he (R-t-regularizedSpatialDistance δ x₀ x)).hasDerivAt.comp_hasFDerivAt x
    ((regularizedSpatialDistance_hasFDerivAt δ x₀ x hδ).const_sub (R-t))
  convert hf using 1
  ext z
  simp [smoothConeCutoffGradient,smoothConeCutoffTimeDerivative]

theorem smoothConeCutoff_energy_sign
    (δ R t : ℝ) (x₀ x : KGSpatialSpace) (hδ : 0 < δ) :
    smoothConeCutoffTimeDerivative δ R t x₀ x+‖smoothConeCutoffGradient δ R t x₀ x‖ ≤ 0 := by
  have he : 0 ≤ deriv Real.smoothTransition (R-t-regularizedSpatialDistance δ x₀ x) :=
    Real.smoothTransition.monotone.deriv_nonneg
  have hn := regularizedDistanceGradient_norm_le_one δ x₀ x hδ
  rw [smoothConeCutoffGradient,norm_smul,Real.norm_eq_abs]
  unfold smoothConeCutoffTimeDerivative
  rw [abs_neg,abs_of_nonneg he]
  nlinarith

theorem smoothConeCutoff_zero_of_norm_le
    (δ R t : ℝ) (x₀ x : KGSpatialSpace) (hx : R-t ≤ ‖x-x₀‖) :
    smoothConeCutoff δ R t x₀ x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith [norm_sub_le_regularizedDistance δ x₀ x]

theorem smoothConeCutoff_pos_at_center
    (δ R t : ℝ) (x₀ : KGSpatialSpace) (hδ : 0 < δ) (hR : t+δ < R) :
    0 < smoothConeCutoff δ R t x₀ x₀ := by
  apply Real.smoothTransition.pos_of_pos
  simp only [regularizedSpatialDistance,sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),
    add_zero,Real.sqrt_sq_eq_abs,abs_of_pos hδ]
  linarith

end AASCKleinGordon
