import KGWeylClosedAlgebra

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem weylOperator_fixes_vacuum_iff (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    weylOperator a g (fockVacuum a)=fockVacuum a ↔ g=0 := by
  constructor
  · intro h
    have hh:=congrArg (fun v : FockHilbert a => inner ℂ (fockVacuum a) v) h
    change inner ℂ (fockVacuum a) (weylOperator a g (fockVacuum a))=
      inner ℂ (fockVacuum a) (fockVacuum a) at hh
    rw [weylOperator_vacuum,normalizedCoherentVector,inner_smul_right,
      ← exponentialVector_zero,exponentialVector_inner,exponentialVector_inner] at hh
    simp only [map_zero,inner_zero_left,Complex.exp_zero,mul_one] at hh
    have he : Real.exp (-‖oneParticleSchwartzToHilbert a g‖^2/2)=1 :=
      Complex.ofReal_injective (by exact hh)
    have hz : -‖oneParticleSchwartzToHilbert a g‖^2/2=0:=
      Real.exp_injective (by simpa only [Real.exp_zero] using he)
    have hn : ‖oneParticleSchwartzToHilbert a g‖=0 := by nlinarith [norm_nonneg (oneParticleSchwartzToHilbert a g)]
    apply oneParticleSchwartz_injective a
    simpa only [map_zero] using norm_eq_zero.mp hn
  · rintro rfl
    rw [weylOperator_zero]
    rfl

/-- An actual nonzero original Schwartz label moves the original vacuum.
The family is not collapsed to identity operators. -/
theorem exists_weyl_displacement_moving_vacuum (a : Parameters) :
    ∃ g : 𝓢(Momentum,ℂ),weylOperator a g (fockVacuum a)≠fockVacuum a := by
  obtain ⟨f,_,hc,hs,_,h0⟩:=exists_contDiff_tsupport_subset
    (E:=Momentum) (x:=0) (n:=⊤) (s:=Set.univ) (by simp)
  let g : 𝓢(Momentum,ℂ):=(hc.comp_left (g:=Complex.ofReal) (by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hs)
  refine ⟨g,?_⟩
  intro hg
  have hz:=(weylOperator_fixes_vacuum_iff a g).mp hg
  have he:=congrArg (fun v : 𝓢(Momentum,ℂ) => v 0) hz
  simpa [g,h0] using he

end AASCKleinGordon
