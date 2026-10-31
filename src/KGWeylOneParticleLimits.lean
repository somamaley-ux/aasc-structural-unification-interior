import KGWeylContinuity

noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
open Filter
open scoped SchwartzMap Topology
namespace AASCKleinGordon

/-- Original one-particle Hilbert convergence suffices; Schwartz convergence is
not assumed. Both the labels and target remain the original Schwartz objects. -/
theorem exponentialVector_tendsto_of_oneParticle {I : Type*} (l : Filter I)
    (a : Parameters) (g : I → 𝓢(Momentum,ℂ)) (g0 : 𝓢(Momentum,ℂ))
    (hg : Tendsto (fun i => oneParticleSchwartzToHilbert a (g i)) l
      (𝓝 (oneParticleSchwartzToHilbert a g0))) :
    Tendsto (fun i => exponentialVector a (g i)) l (𝓝 (exponentialVector a g0)) := by
  have hs : Tendsto (fun i => ‖exponentialVector a (g i)-exponentialVector a g0‖^2) l
      (𝓝 (‖exponentialVector a g0-exponentialVector a g0‖^2)) := by
    simp_rw [norm_sub_sq (𝕜:=ℂ),exponentialVector_norm_sq,exponentialVector_inner]
    exact ((Real.continuous_exp.tendsto _ |>.comp (hg.norm.pow 2)).sub
      (tendsto_const_nhds.mul (Complex.continuous_re.tendsto _ |>.comp
        (Complex.continuous_exp.tendsto _ |>.comp (hg.inner tendsto_const_nhds))))).add
      tendsto_const_nhds
  have hn:=Real.continuous_sqrt.tendsto _ |>.comp hs
  rw [← tendsto_sub_nhds_zero_iff]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,sub_self,norm_zero,zero_pow,
    Real.sqrt_zero,abs_zero] using hn

theorem weylCoherentImage_tendsto_of_oneParticle {I : Type*} (l : Filter I)
    (a : Parameters) (g : I → 𝓢(Momentum,ℂ)) (g0 f : 𝓢(Momentum,ℂ))
    (hg : Tendsto (fun i => oneParticleSchwartzToHilbert a (g i)) l
      (𝓝 (oneParticleSchwartzToHilbert a g0))) :
    Tendsto (fun i => weylCoherentImage a (g i) f) l (𝓝 (weylCoherentImage a g0 f)) := by
  unfold weylCoherentImage
  have ha : Tendsto (fun i => oneParticleSchwartzToHilbert a (f+g i)) l
      (𝓝 (oneParticleSchwartzToHilbert a (f+g0))) := by
    simpa only [map_add] using tendsto_const_nhds.add hg
  have hc : Tendsto (fun i => Complex.exp
      (-((‖oneParticleSchwartzToHilbert a (g i)‖^2/2 : ℝ) : ℂ)-
        inner ℂ (oneParticleSchwartzToHilbert a (g i)) (oneParticleSchwartzToHilbert a f))) l
      (𝓝 (Complex.exp (-((‖oneParticleSchwartzToHilbert a g0‖^2/2 : ℝ) : ℂ)-
        inner ℂ (oneParticleSchwartzToHilbert a g0) (oneParticleSchwartzToHilbert a f)))) :=
    Complex.continuous_exp.tendsto _ |>.comp
    ((Complex.continuous_ofReal.tendsto _ |>.comp ((hg.norm.pow 2).div_const 2)).neg.sub
      (hg.inner tendsto_const_nhds))
  exact hc.smul (exponentialVector_tendsto_of_oneParticle l a _ _ ha)

theorem weylOperator_span_tendsto_of_oneParticle {I : Type*} (l : Filter I)
    (a : Parameters) (g : I → 𝓢(Momentum,ℂ)) (g0 : 𝓢(Momentum,ℂ))
    (hg : Tendsto (fun i => oneParticleSchwartzToHilbert a (g i)) l
      (𝓝 (oneParticleSchwartzToHilbert a g0))) (u : coherentSpan a) :
    Tendsto (fun i => weylOperator a (g i) (u : FockHilbert a)) l
      (𝓝 (weylOperator a g0 (u : FockHilbert a))) := by
  obtain ⟨v,⟨c,rfl⟩⟩:=u
  simp only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul]
  apply tendsto_finset_sum
  intro f _
  simpa only [weylOperator_exponentialVector] using
    tendsto_const_nhds.smul (weylCoherentImage_tendsto_of_oneParticle l a g g0 f hg)

/-- Strong convergence of the actual bounded operators under one-particle L2
label convergence. This does not assert operator-norm convergence. -/
theorem weylOperator_tendsto_of_oneParticle {I : Type*} (l : Filter I)
    (a : Parameters) (g : I → 𝓢(Momentum,ℂ)) (g0 : 𝓢(Momentum,ℂ))
    (hg : Tendsto (fun i => oneParticleSchwartzToHilbert a (g i)) l
      (𝓝 (oneParticleSchwartzToHilbert a g0))) (v : FockHilbert a) :
    Tendsto (fun i => weylOperator a (g i) v) l (𝓝 (weylOperator a g0 v)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨w,⟨u,rfl⟩,hu⟩:=Metric.mem_closure_iff.mp (coherentSpan_subtype_dense a v)
    (ε/3) (by positivity)
  have hh:=Metric.tendsto_nhds.mp (weylOperator_span_tendsto_of_oneParticle l a g g0 hg u)
    (ε/3) (by positivity)
  filter_upwards [hh] with i hi
  have hd (h : 𝓢(Momentum,ℂ)) (x y : FockHilbert a) :
      dist (weylOperator a h x) (weylOperator a h y)=dist x y :=
    (weylUnitary a h).isometry.dist_eq x y
  have ht:=dist_triangle4 (weylOperator a (g i) v) (weylOperator a (g i) u)
    (weylOperator a g0 u) (weylOperator a g0 v)
  rw [hd,hd,dist_comm (u : FockHilbert a) v] at ht
  change dist v (u : FockHilbert a)<ε/3 at hu
  linarith

theorem weyl_commutation_passes_to_oneParticle_limit {I : Type*} (l : Filter I) [l.NeBot]
    (a : Parameters) (g : I → 𝓢(Momentum,ℂ)) (g0 : 𝓢(Momentum,ℂ))
    (hg : Tendsto (fun i => oneParticleSchwartzToHilbert a (g i)) l
      (𝓝 (oneParticleSchwartzToHilbert a g0)))
    (T : FockHilbert a →L[ℂ] FockHilbert a)
    (hc : ∀ i,T * weylOperator a (g i)=weylOperator a (g i) * T) :
    T * weylOperator a g0=weylOperator a g0 * T := by
  apply ContinuousLinearMap.ext
  intro v
  have h1:=(T.continuous.tendsto _).comp (weylOperator_tendsto_of_oneParticle l a g g0 hg v)
  have h2:=weylOperator_tendsto_of_oneParticle l a g g0 hg (T v)
  have h2' : Tendsto (fun i => T (weylOperator a (g i) v)) l
      (𝓝 (weylOperator a g0 (T v))) := by
    convert h2 using 1
    funext i
    exact congrArg (fun A : FockHilbert a →L[ℂ] FockHilbert a => A v) (hc i)
  exact tendsto_nhds_unique h1 h2'

end AASCKleinGordon
