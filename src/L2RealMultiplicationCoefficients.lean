import L2BoundedMultiplicationAlgebra
import L2RealMultiplicationGraph
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open MeasureTheory Filter
namespace AASCKleinGordon
namespace Multiplication

def graphDenominator (r : ℝ) : ℝ := Real.sqrt (1+r^2)
def graphCoefficientB (r : ℝ) : ℂ := (1/graphDenominator r : ℝ)
def graphCoefficientA (r : ℝ) : ℂ := (r : ℂ)*graphCoefficientB r

theorem graphDenominator_pos (r : ℝ) : 0<graphDenominator r := by
  apply Real.sqrt_pos.mpr
  positivity

theorem graphDenominator_ge_one (r : ℝ) : 1≤graphDenominator r := by
  have hs := Real.sq_sqrt (by positivity : 0≤1+r^2)
  have hp := graphDenominator_pos r
  change graphDenominator r^2=1+r^2 at hs
  nlinarith [sq_nonneg r]

theorem abs_le_graphDenominator (r : ℝ) : |r|≤graphDenominator r := by
  have hs := Real.sq_sqrt (by positivity : 0≤1+r^2)
  have hp := graphDenominator_pos r
  change graphDenominator r^2=1+r^2 at hs
  nlinarith [sq_abs r,abs_nonneg r]

theorem graphCoefficientB_bound (r : ℝ) : ‖graphCoefficientB r‖≤1 := by
  rw [graphCoefficientB,Complex.norm_real,Real.norm_eq_abs,abs_of_pos
    (div_pos zero_lt_one (graphDenominator_pos r))]
  exact (div_le_one (graphDenominator_pos r)).2 (graphDenominator_ge_one r)

theorem graphCoefficientA_bound (r : ℝ) : ‖graphCoefficientA r‖≤1 := by
  have he : ‖graphCoefficientA r‖=|r|/graphDenominator r := by
    simp [graphCoefficientA,graphCoefficientB,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (graphDenominator_pos r),div_eq_mul_inv]
  rw [he]
  exact (div_le_one (graphDenominator_pos r)).2 (abs_le_graphDenominator r)

theorem graphCoefficientB_ne_zero (r : ℝ) : graphCoefficientB r≠0 := by
  change ((1/graphDenominator r : ℝ) : ℂ)≠0
  exact_mod_cast ne_of_gt (div_pos zero_lt_one (graphDenominator_pos r))

@[simp] theorem graphCoefficientB_real (r : ℝ) : star (graphCoefficientB r)=graphCoefficientB r := by
  simp [graphCoefficientB]

@[simp] theorem graphCoefficientA_real (r : ℝ) : star (graphCoefficientA r)=graphCoefficientA r := by
  simp [graphCoefficientA]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem graphCoefficientB_measurable (v : X → ℝ) (hv : Measurable v) :
    Measurable (fun x => graphCoefficientB (v x)) := by
  unfold graphCoefficientB graphDenominator
  fun_prop

theorem graphCoefficientA_measurable (v : X → ℝ) (hv : Measurable v) :
    Measurable (fun x => graphCoefficientA (v x)) :=
  (Complex.measurable_ofReal.comp hv).mul (graphCoefficientB_measurable v hv)

def graphBoundedB (v : X → ℝ) (hv : Measurable v) : H μ →L[ℂ] H μ :=
  boundedMul (fun x => graphCoefficientB (v x)) (graphCoefficientB_measurable v hv).aestronglyMeasurable
    1 (Eventually.of_forall (fun x => graphCoefficientB_bound (v x)))

def graphBoundedA (v : X → ℝ) (hv : Measurable v) : H μ →L[ℂ] H μ :=
  boundedMul (fun x => graphCoefficientA (v x)) (graphCoefficientA_measurable v hv).aestronglyMeasurable
    1 (Eventually.of_forall (fun x => graphCoefficientA_bound (v x)))

theorem graphBoundedB_ae (v : X → ℝ) (hv : Measurable v) (f : H μ) :
    graphBoundedB v hv f=ᵐ[μ] (fun x => graphCoefficientB (v x)*f x) := boundedMul_ae _ _ _ _ f

theorem graphBoundedA_ae (v : X → ℝ) (hv : Measurable v) (f : H μ) :
    graphBoundedA v hv f=ᵐ[μ] (fun x => graphCoefficientA (v x)*f x) := boundedMul_ae _ _ _ _ f

end Multiplication
end AASCKleinGordon
