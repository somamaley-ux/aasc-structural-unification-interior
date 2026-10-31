import KGWeylGeneratorSymmetry
import ClosureOfEssentiallySelfAdjoint

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

/-- The actual orbit generator restricted to the actual invariant coherent span. -/
def weylCoherentCoreGenerator (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    FockHilbert a →ₗ.[ℂ] FockHilbert a where
  domain:=coherentSpan a
  toFun:=(weylOrbitGenerator a g).toFun.comp
    (Submodule.inclusion (coherentSpan_le_weylStrongOrbitDomain a g))

theorem weylCoherentCoreGenerator_apply (a : Parameters) (g : 𝓢(Momentum,ℂ))
    (x : (weylCoherentCoreGenerator a g).domain) :
    weylCoherentCoreGenerator a g x=weylOrbitGenerator a g
      ⟨x.val,coherentSpan_le_weylStrongOrbitDomain a g x.property⟩ := rfl

theorem weylCoherentCoreGenerator_domain_invariant (a : Parameters) (g : 𝓢(Momentum,ℂ))
    (r : ℝ) (x : (weylCoherentCoreGenerator a g).domain) :
    weylRealLine a g r x.val∈(weylCoherentCoreGenerator a g).domain := by
  change weylOperator a ((r : ℂ) • g) x.val∈coherentSpan a
  exact weylOperator_preserves_coherentSpan a ((r : ℂ) • g) x

theorem weylCoherentCoreGenerator_commute (a : Parameters) (g : 𝓢(Momentum,ℂ))
    (r : ℝ) (x : (weylCoherentCoreGenerator a g).domain) :
    weylCoherentCoreGenerator a g
      ⟨weylRealLine a g r x.val,weylCoherentCoreGenerator_domain_invariant a g r x⟩=
        weylRealLine a g r (weylCoherentCoreGenerator a g x) :=
  weylOrbitGenerator_commute a g r ⟨x.val,coherentSpan_le_weylStrongOrbitDomain a g x.property⟩

theorem weylCoherentCoreGenerator_hasDerivAt (a : Parameters) (g : 𝓢(Momentum,ℂ))
    (x : (weylCoherentCoreGenerator a g).domain) (r : ℝ) :
    HasDerivAt (fun t : ℝ => weylRealLine a g t x.val)
      (Complex.I • weylRealLine a g r (weylCoherentCoreGenerator a g x)) r :=
  weylOrbitGenerator_hasDerivAt a g ⟨x.val,coherentSpan_le_weylStrongOrbitDomain a g x.property⟩ r

theorem weylCoherentCoreGenerator_symmetric (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    (weylCoherentCoreGenerator a g).IsFormalAdjoint (weylCoherentCoreGenerator a g) := by
  intro x y
  exact weylOrbitGenerator_symmetric a g
    ⟨x.val,coherentSpan_le_weylStrongOrbitDomain a g x.property⟩
    ⟨y.val,coherentSpan_le_weylStrongOrbitDomain a g y.property⟩

theorem weylCoherentCoreGenerator_adjoint_selfAdjoint (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    IsSelfAdjoint (weylCoherentCoreGenerator a g).adjoint :=
  UnitaryCore.adjoint_selfAdjoint_of_unitary_core Complex.I Complex.I_ne_zero (by simp)
    (weylRealLine a g) (weylRealLine_strongly_continuous a g)
    (weylRealLine_zero a g) (weylRealLine_symm a g)
    (weylCoherentCoreGenerator a g) (coherentSpan_dense a)
    (weylCoherentCoreGenerator_symmetric a g)
    (weylCoherentCoreGenerator_domain_invariant a g)
    (weylCoherentCoreGenerator_commute a g)
    (weylCoherentCoreGenerator_hasDerivAt a g)

theorem weylCoherentCoreGenerator_closure_eq_adjoint (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    (weylCoherentCoreGenerator a g).closure=(weylCoherentCoreGenerator a g).adjoint :=
  UnitaryCore.closure_eq_adjoint_of_selfAdjoint_adjoint (weylCoherentCoreGenerator a g)
    (coherentSpan_dense a) (weylCoherentCoreGenerator_symmetric a g)
    (weylCoherentCoreGenerator_adjoint_selfAdjoint a g)

theorem weylCoherentCoreGenerator_adjoint_hasDerivAt (a : Parameters) (g : 𝓢(Momentum,ℂ))
    (x : (weylCoherentCoreGenerator a g).adjoint.domain) (r : ℝ) :
    HasDerivAt (fun t : ℝ => weylRealLine a g t x.val)
      (Complex.I • weylRealLine a g r ((weylCoherentCoreGenerator a g).adjoint x)) r :=
  UnitaryCore.adjoint_orbit_hasDerivAt Complex.I (by simp) (weylRealLine a g)
    (weylRealLine_strongly_continuous a g) (weylRealLine_symm a g)
    (weylCoherentCoreGenerator a g) (coherentSpan_dense a)
    (weylCoherentCoreGenerator_domain_invariant a g)
    (weylCoherentCoreGenerator_commute a g)
    (weylCoherentCoreGenerator_hasDerivAt a g) x r

end AASCKleinGordon
