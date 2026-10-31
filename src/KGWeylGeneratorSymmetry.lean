import KGWeylOrbitGenerator

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem weylOrbitGenerator_domain_invariant (a : Parameters) (g : 𝓢(Momentum,ℂ))
    (r : ℝ) (x : (weylOrbitGenerator a g).domain) :
    weylRealLine a g r x.val∈(weylOrbitGenerator a g).domain :=
  weylStrongOrbitDomain_invariant a g r x

theorem weylOrbitGenerator_commute (a : Parameters) (g : 𝓢(Momentum,ℂ))
    (r : ℝ) (x : (weylOrbitGenerator a g).domain) :
    weylOrbitGenerator a g ⟨weylRealLine a g r x.val,weylOrbitGenerator_domain_invariant a g r x⟩=
      weylRealLine a g r (weylOrbitGenerator a g x) := by
  have hc:=((weylRealLine a g r).toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (weylOrbitGenerator_hasDerivAt_zero a g x)
  have he : (fun t : ℝ => weylRealLine a g r (weylRealLine a g t x.val))=
      (fun t : ℝ => weylRealLine a g t (weylRealLine a g r x.val)) := by
    funext t
    rw [← weylRealLine_add,← weylRealLine_add,add_comm r t]
  change HasDerivAt (fun t : ℝ => weylRealLine a g r (weylRealLine a g t x.val))
    (weylRealLine a g r (Complex.I • weylOrbitGenerator a g x)) 0 at hc
  rw [he,map_smul] at hc
  have hx:=weylOrbitGenerator_hasDerivAt_zero a g
    ⟨weylRealLine a g r x.val,weylOrbitGenerator_domain_invariant a g r x⟩
  have hh:=congrArg (fun v : FockHilbert a => (-Complex.I) • v) (hx.unique hc)
  simpa only [smul_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul] using hh

theorem weylOrbitGenerator_symmetric (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    (weylOrbitGenerator a g).IsFormalAdjoint (weylOrbitGenerator a g) := by
  intro x y
  have hx:=weylOrbitGenerator_hasDerivAt_zero a g x
  have hy:=weylOrbitGenerator_hasDerivAt_zero a g y
  have hh:=hx.inner ℂ hy
  have hc : HasDerivAt (fun t : ℝ => inner ℂ (weylRealLine a g t x.val)
      (weylRealLine a g t y.val)) 0 0 := by
    simpa only [LinearIsometryEquiv.inner_map_map] using
      hasDerivAt_const (0 : ℝ) (inner ℂ x.val y.val)
  have he:=hh.unique hc
  simp only [weylRealLine_zero,inner_smul_left,inner_smul_right,Complex.conj_I] at he
  have hm : Complex.I*(inner ℂ x.val (weylOrbitGenerator a g y)-
      inner ℂ (weylOrbitGenerator a g x) y.val)=0 := by
    linear_combination he
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left Complex.I_ne_zero)).symm

end AASCKleinGordon
