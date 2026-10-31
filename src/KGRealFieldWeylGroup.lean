import KGRealSmearingWeylAlgebra
import KGSpacetimeFieldAdjoint

noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

theorem weylPhase_real_line (a : Parameters) (g : 𝓢(Momentum,ℂ)) (t r : ℝ) :
    weylPhase a ((t : ℂ) • g) ((r : ℂ) • g)=1 := by
  unfold weylPhase
  simp only [map_smul,inner_smul_left,inner_smul_right,Complex.conj_ofReal]
  have hz : (t : ℂ)*((r : ℂ)*inner ℂ (oneParticleSchwartzToHilbert a g)
      (oneParticleSchwartzToHilbert a g))-
      (r : ℂ)*((t : ℂ)*inner ℂ (oneParticleSchwartzToHilbert a g)
        (oneParticleSchwartzToHilbert a g))=0 := by ring
  rw [hz,zero_div,Complex.exp_zero]

def weylRealLine (a : Parameters) (g : 𝓢(Momentum,ℂ)) (t : ℝ) :
    FockHilbert a ≃ₗᵢ[ℂ] FockHilbert a := weylUnitary a ((t : ℂ) • g)

theorem weylRealLine_zero (a : Parameters) (g : 𝓢(Momentum,ℂ)) (v : FockHilbert a) :
    weylRealLine a g 0 v=v := by
  change weylOperator a ((0 : ℂ) • g) v=v
  rw [zero_smul,weylOperator_zero]
  rfl

theorem weylRealLine_symm (a : Parameters) (g : 𝓢(Momentum,ℂ)) (t : ℝ) (v : FockHilbert a) :
    (weylRealLine a g t).symm v=weylRealLine a g (-t) v := by
  change weylOperator a (-((t : ℂ) • g)) v=weylOperator a (((-t : ℝ) : ℂ) • g) v
  rw [Complex.ofReal_neg,neg_smul]

theorem weylRealLine_add (a : Parameters) (g : 𝓢(Momentum,ℂ)) (t r : ℝ) (v : FockHilbert a) :
    weylRealLine a g (t+r) v=weylRealLine a g t (weylRealLine a g r v) := by
  have hh:=weylOperator_mul a ((t : ℂ) • g) ((r : ℂ) • g)
  rw [weylPhase_real_line,one_smul] at hh
  have he:=congrArg (fun T : FockHilbert a →L[ℂ] FockHilbert a => T v) hh
  change weylOperator a ((t : ℂ) • g) (weylOperator a ((r : ℂ) • g) v)=
    weylOperator a ((t : ℂ) • g+(r : ℂ) • g) v at he
  simpa only [weylRealLine,Complex.ofReal_add,add_smul] using he.symm

theorem weylRealLine_strongly_continuous (a : Parameters) (g : 𝓢(Momentum,ℂ)) (v : FockHilbert a) :
    Continuous (fun t : ℝ => weylRealLine a g t v) := by
  exact (weylOperator_strongly_continuous a v).comp
    (Complex.continuous_ofReal.smul continuous_const)

theorem weylOperator_preserves_coherentSpan (a : Parameters) (g : 𝓢(Momentum,ℂ))
    (u : coherentSpan a) : weylOperator a g (u : FockHilbert a)∈coherentSpan a := by
  have hh : coherentSpan a≤(coherentSpan a).comap (weylOperator a g).toLinearMap := by
    rw [coherentSpan_eq_span]
    apply Submodule.span_le.mpr
    rintro v ⟨f,rfl⟩
    change weylOperator a g (exponentialVector a f)∈Submodule.span ℂ (Set.range (exponentialVector a))
    rw [← coherentSpan_eq_span a]
    rw [weylOperator_exponentialVector]
    exact (coherentSpan a).smul_mem _ (exponentialVector_mem_coherentSpan a (f+g))
  exact hh u.property

def realFieldWeylGroup (a : Parameters) (s : ℝ) (h : realSpacetimeTestSpace) (t : ℝ) :
    FockHilbert a ≃ₗᵢ[ℂ] FockHilbert a :=
  weylRealLine a (realFieldWeylLabelCLM a s h) t

theorem original_real_field_segal (a : Parameters) (s : ℝ) (h : realSpacetimeTestSpace) :
    spacetimeFieldCore a s h.val=(s : ℂ) •
      (creationCore (originalRealSmearingCLM a h)+annihilationCore a (originalRealSmearingCLM a h)) := by
  have hr:=(mem_realSpacetimeTestSpace h.val).mp h.property
  simp only [spacetimeFieldCore,hr]
  rfl

/-- Exact algebraic sign/scale identification on the ORIGINAL finite-particle
core. The analytic orbit derivative must still be proved; it is not assumed here. -/
theorem imaginary_creation_annihilation_difference (a : Parameters) (s : ℝ)
    (h : realSpacetimeTestSpace) :
    creationCore (realFieldWeylLabelCLM a s h)-annihilationCore a (realFieldWeylLabelCLM a s h)=
      Complex.I • spacetimeFieldCore a s h.val := by
  rw [original_real_field_segal]
  change creationCore ((Complex.I*(s : ℂ)) • originalRealSmearingCLM a h)-
      annihilationCore a ((Complex.I*(s : ℂ)) • originalRealSmearingCLM a h)=_
  rw [creationCore_smul_smear,annihilationCore_smul_smear]
  have hs : star (Complex.I*(s : ℂ))= -(Complex.I*(s : ℂ)) := by
    simp
  rw [hs]
  module

end AASCKleinGordon
