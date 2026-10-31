import UnboundedChargeGeneratorUniqueness
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Add

noncomputable section
namespace AASCKleinGordon.GlobalCharge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem differentiable_orbit_mem_selfAdjoint_domain
    (κ : ℂ) (hκ : κ≠0) (hstar : star (-κ)=κ)
    (U : ℝ → H ≃ₗᵢ[ℂ] H) (hzero : ∀ x,U 0 x=x)
    (hinv : ∀ t x,(U t).symm x=U (-t) x)
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T)
    (hforward : ∀ x : T.domain,HasDerivAt (fun t => U t x.val) (κ • T x) 0)
    (f : H) (hf : DifferentiableAt ℝ (fun t => U t f) 0) : f ∈ T.domain := by
  let z := deriv (fun t => U t f) 0
  have hderiv : HasDerivAt (fun t => U t f) z 0 := hf.hasDerivAt
  have ha : f ∈ T.adjoint.domain := by
    apply LinearPMap.mem_adjoint_domain_of_exists f
    refine ⟨κ⁻¹ • z,?_⟩
    intro y
    have hyneg : HasDerivAt (fun t => U (-t) y.val) ((-κ) • T y) 0 := by
      have hn : HasDerivAt (fun t : ℝ => -t) (-1 : ℝ) 0 :=
        HasDerivAt.neg (hasDerivAt_id (0 : ℝ))
      have hy : HasDerivAt (fun t => U t y.val) (κ • T y) (-(0 : ℝ)) := by simpa using hforward y
      have h := hy.scomp (0 : ℝ) hn
      simpa only [Function.comp_def,neg_zero,neg_smul,neg_one_smul,one_smul] using h
    have hleft : HasDerivAt (fun t => inner ℂ y.val (U t f)) (inner ℂ y.val z) 0 := by
      simpa using (hasDerivAt_const (0 : ℝ) y.val).inner ℂ hderiv
    have hright : HasDerivAt (fun t => inner ℂ (U (-t) y.val) f)
        (κ*inner ℂ (T y) f) 0 := by
      have hstar' : (starRingEnd ℂ) (-κ)=κ := hstar
      simpa only [inner_zero_right,zero_add,inner_smul_left,hstar'] using
        hyneg.inner ℂ (hasDerivAt_const (0 : ℝ) f)
    have heq : (fun t => inner ℂ y.val (U t f))=(fun t => inner ℂ (U (-t) y.val) f) := by
      funext t
      have h := (U t).inner_map_map ((U t).symm y.val) f
      rw [LinearIsometryEquiv.apply_symm_apply] at h
      simpa only [hinv] using h
    rw [← heq] at hright
    have hs := hleft.unique hright
    have hw : inner ℂ y.val (κ⁻¹ • z)=inner ℂ (T y) f := by
      rw [inner_smul_right,hs,← mul_assoc,inv_mul_cancel₀ hκ,one_mul]
    simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) hw
  rwa [LinearPMap.isSelfAdjoint_def.mp hT] at ha

end AASCKleinGordon.GlobalCharge
