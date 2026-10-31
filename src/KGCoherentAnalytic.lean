import ComplexEntireSeriesRigidity
import KGCoherentTotality
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem coherentScalar_hasSum (a : Parameters) (v : FockHilbert a)
    (f : 𝓢(Momentum,ℂ)) (z : ℂ) :
    HasSum (fun n => inner ℂ (v n) (coherentSector a f n)*z^n)
      (inner ℂ v (exponentialVector a (z • f))) := by
  simpa only [exponentialVector_component,coherentSector_smul,inner_smul_right,mul_comm]
    using lp.hasSum_inner (𝕜:=ℂ) v (exponentialVector a (z • f))

theorem coherentScalar_differentiable (a : Parameters) (v : FockHilbert a)
    (f : 𝓢(Momentum,ℂ)) :
    Differentiable ℂ (fun z : ℂ => inner ℂ v (exponentialVector a (z • f))) :=
  complex_series_differentiable _ _ (coherentScalar_hasSum a v f)

theorem boundedCoherentScalar_differentiable (a : Parameters) (v : FockHilbert a)
    (T : FockHilbert a →L[ℂ] FockHilbert a) (f : 𝓢(Momentum,ℂ)) :
    Differentiable ℂ (fun z : ℂ => inner ℂ v (T (exponentialVector a (z • f)))) := by
  simpa only [ContinuousLinearMap.adjoint_inner_left] using
    coherentScalar_differentiable a (T.adjoint v) f

end AASCKleinGordon
