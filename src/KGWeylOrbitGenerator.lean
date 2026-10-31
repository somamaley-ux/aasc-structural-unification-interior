import KGWeylStrongDomain
import UnitaryInvariantCoreAdjoint

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

/-- Actual maximal orbit generator, with the self-adjoint convention T=-iD.
Its domain is the already constructed strong differentiability domain. -/
def weylOrbitGenerator (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    FockHilbert a →ₗ.[ℂ] FockHilbert a where
  domain:=weylStrongOrbitDomain a g
  toFun:=
    { toFun:=fun x => (-Complex.I) • deriv (fun t : ℝ => weylRealLine a g t x.val) 0
      map_add':=by
        intro x y
        have hx:=x.property.hasDerivAt
        have hy:=y.property.hasDerivAt
        have hh : HasDerivAt (fun t : ℝ => weylRealLine a g t (x.val+y.val))
            (deriv (fun t : ℝ => weylRealLine a g t x.val) 0+
             deriv (fun t : ℝ => weylRealLine a g t y.val) 0) 0 := by
          simpa only [map_add,Pi.add_apply] using hx.add hy
        change (-Complex.I) • deriv (fun t : ℝ => weylRealLine a g t (x.val+y.val)) 0=_
        rw [hh.deriv]
        exact smul_add _ _ _
      map_smul':=by
        intro c x
        have hx:=x.property.hasDerivAt
        have hc:=((c • ContinuousLinearMap.id ℂ (FockHilbert a)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hx
        have hh : HasDerivAt (fun t : ℝ => weylRealLine a g t (c • x.val))
            (c • deriv (fun t : ℝ => weylRealLine a g t x.val) 0) 0 := by
          simpa only [Function.comp_def,ContinuousLinearMap.coe_restrictScalars',
            ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,map_smul] using hc
        change (-Complex.I) • deriv (fun t : ℝ => weylRealLine a g t (c • x.val)) 0=_
        rw [hh.deriv]
        simp only [RingHom.id_apply]
        exact smul_comm _ _ _ }

theorem weylOrbitGenerator_apply (a : Parameters) (g : 𝓢(Momentum,ℂ))
    (x : (weylOrbitGenerator a g).domain) :
    weylOrbitGenerator a g x=(-Complex.I) • deriv (fun t : ℝ => weylRealLine a g t x.val) 0 := rfl

theorem weylOrbitGenerator_domain_dense (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    Dense ((weylOrbitGenerator a g).domain : Set (FockHilbert a)) := weylStrongOrbitDomain_dense a g

theorem weylOrbitGenerator_hasDerivAt_zero (a : Parameters) (g : 𝓢(Momentum,ℂ))
    (x : (weylOrbitGenerator a g).domain) :
    HasDerivAt (fun t : ℝ => weylRealLine a g t x.val) (Complex.I • weylOrbitGenerator a g x) 0 := by
  have hx:=x.property.hasDerivAt
  rw [weylOrbitGenerator_apply]
  simpa only [smul_smul,mul_neg,Complex.I_mul_I,neg_neg,one_smul] using hx

theorem weylOrbitGenerator_hasDerivAt (a : Parameters) (g : 𝓢(Momentum,ℂ))
    (x : (weylOrbitGenerator a g).domain) (r : ℝ) :
    HasDerivAt (fun t : ℝ => weylRealLine a g t x.val)
      (Complex.I • weylRealLine a g r (weylOrbitGenerator a g x)) r := by
  simpa only [map_smul] using weylRealLine_hasDerivAt_of_zero a g x.val _
    (weylOrbitGenerator_hasDerivAt_zero a g x) r

end AASCKleinGordon
