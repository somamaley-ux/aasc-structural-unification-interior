import KGWeylCoherentDerivative

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

/-- The actual strong orbit differentiability domain; no received generator. -/
def weylStrongOrbitDomain (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    Submodule ℂ (FockHilbert a) where
  carrier := {v | DifferentiableAt ℝ (fun t : ℝ => weylRealLine a g t v) 0}
  zero_mem' := by
    change DifferentiableAt ℝ (fun t : ℝ => weylRealLine a g t 0) 0
    have hh : DifferentiableAt ℝ (fun _ : ℝ => (0 : FockHilbert a)) 0 := differentiableAt_const _
    simpa only [map_zero] using hh
  add_mem' := by
    intro x y hx hy
    change DifferentiableAt ℝ (fun t : ℝ => weylRealLine a g t (x+y)) 0
    simpa only [map_add,Pi.add_apply] using hx.add hy
  smul_mem' := by
    intro c x hx
    change DifferentiableAt ℝ (fun t : ℝ => weylRealLine a g t (c • x)) 0
    have hh:=(((c • ContinuousLinearMap.id ℂ (FockHilbert a)).restrictScalars ℝ).differentiableAt).comp 0 hx
    simpa only [ContinuousLinearMap.coe_restrictScalars',ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply,map_smul,Function.comp_def] using hh

theorem coherentSpan_le_weylStrongOrbitDomain (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    coherentSpan a≤weylStrongOrbitDomain a g := by
  rw [coherentSpan_eq_span]
  apply Submodule.span_le.mpr
  rintro v ⟨f,rfl⟩
  exact (weylRealLine_exponentialVector_hasDerivAt_zero a g f).differentiableAt

theorem weylStrongOrbitDomain_dense (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    Dense (weylStrongOrbitDomain a g : Set (FockHilbert a)) :=
  (coherentSpan_dense a).mono (coherentSpan_le_weylStrongOrbitDomain a g)

/-- Transport an actual strong derivative at zero to every group parameter. -/
theorem weylRealLine_hasDerivAt_of_zero (a : Parameters) (g : 𝓢(Momentum,ℂ))
    (v B : FockHilbert a)
    (h0 : HasDerivAt (fun t : ℝ => weylRealLine a g t v) B 0) (r : ℝ) :
    HasDerivAt (fun t : ℝ => weylRealLine a g t v) (weylRealLine a g r B) r := by
  have hr:=((weylRealLine a g r).toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h0
  change HasDerivAt (fun t : ℝ => weylRealLine a g r (weylRealLine a g t v))
    (weylRealLine a g r B) 0 at hr
  have hs : HasDerivAt (fun t : ℝ => t-r) 1 r := (hasDerivAt_id r).sub_const r
  have hh:=hr.scomp_of_eq r hs (by simp)
  have he : (fun t : ℝ => weylRealLine a g r (weylRealLine a g (t-r) v))=
      (fun t : ℝ => weylRealLine a g t v) := by
    funext t
    rw [← weylRealLine_add]
    congr 1
    ring
  simp only [Function.comp_def,sub_self,one_smul] at hh
  simpa only [he] using hh

theorem weylStrongOrbitDomain_invariant (a : Parameters) (g : 𝓢(Momentum,ℂ)) (r : ℝ)
    (v : weylStrongOrbitDomain a g) :
    weylRealLine a g r v.val∈weylStrongOrbitDomain a g := by
  change DifferentiableAt ℝ (fun t : ℝ => weylRealLine a g t (weylRealLine a g r v.val)) 0
  have hh:=((weylRealLine a g r).toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ).differentiableAt.comp 0 v.property
  have he : (fun t : ℝ => weylRealLine a g r (weylRealLine a g t v.val))=
      (fun t : ℝ => weylRealLine a g t (weylRealLine a g r v.val)) := by
    funext t
    rw [← weylRealLine_add,← weylRealLine_add,add_comm r t]
  change DifferentiableAt ℝ (fun t : ℝ => weylRealLine a g r (weylRealLine a g t v.val)) 0 at hh
  rw [he] at hh
  exact hh

/-- The original field-vacuum attachment transported to all parameters. -/
theorem original_real_field_vacuum_weyl_derivative_all (a : Parameters) (s : ℝ)
    (h : realSpacetimeTestSpace) (r : ℝ) :
    HasDerivAt (fun t : ℝ => realFieldWeylGroup a s h t (fockVacuum a))
      (Complex.I • realFieldWeylGroup a s h r
        (finiteParticleCoreToFock a (spacetimeFieldCore a s h.val vacuumCore))) r := by
  simpa only [map_smul] using weylRealLine_hasDerivAt_of_zero a (realFieldWeylLabelCLM a s h)
    (fockVacuum a) _ (original_real_field_vacuum_weyl_derivative a s h) r

end AASCKleinGordon
