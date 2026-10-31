import L2RealMultiplicationCoefficients

noncomputable section
open MeasureTheory Filter
namespace AASCKleinGordon.Multiplication

theorem graphCoefficient_normalized (r : ℝ) :
    graphCoefficientA r*graphCoefficientA r+graphCoefficientB r*graphCoefficientB r=1 := by
  have hd := graphDenominator_pos r
  have hs := Real.sq_sqrt (by positivity : 0≤1+r^2)
  change graphDenominator r^2=1+r^2 at hs
  have hr : (r*(1/graphDenominator r))*(r*(1/graphDenominator r))+
      (1/graphDenominator r)*(1/graphDenominator r)=1 := by
    field_simp
    nlinarith
  dsimp [graphCoefficientA,graphCoefficientB]
  exact_mod_cast hr

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem graphBounded_commute (v : X → ℝ) (hv : Measurable v) :
    (graphBoundedB (μ:=μ) v hv).comp (graphBoundedA v hv)=
      (graphBoundedA v hv).comp (graphBoundedB v hv) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [graphBoundedB_ae v hv (graphBoundedA v hv f),
    graphBoundedA_ae v hv (graphBoundedB v hv f),graphBoundedB_ae v hv f,
    graphBoundedA_ae v hv f] with x h1 h2 h3 h4
  change (graphBoundedB v hv (graphBoundedA v hv f)) x=
    (graphBoundedA v hv (graphBoundedB v hv f)) x
  rw [h1,h2,h3,h4]
  ring

theorem graphBounded_normalized (v : X → ℝ) (hv : Measurable v) :
    (graphBoundedA (μ:=μ) v hv).comp (graphBoundedA v hv)+
      (graphBoundedB v hv).comp (graphBoundedB v hv)=ContinuousLinearMap.id ℂ (H μ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (graphBoundedA v hv (graphBoundedA v hv f))
      (graphBoundedB v hv (graphBoundedB v hv f)),
    graphBoundedA_ae v hv (graphBoundedA v hv f),
    graphBoundedB_ae v hv (graphBoundedB v hv f),graphBoundedA_ae v hv f,
    graphBoundedB_ae v hv f] with x h1 h2 h3 h4 h5
  change ((graphBoundedA v hv (graphBoundedA v hv f))+
    (graphBoundedB v hv (graphBoundedB v hv f))) x=f x
  simp only [Pi.add_apply] at h1
  rw [h1,h2,h3,h4,h5,← mul_assoc,← mul_assoc,← add_mul,graphCoefficient_normalized,one_mul]

end AASCKleinGordon.Multiplication
