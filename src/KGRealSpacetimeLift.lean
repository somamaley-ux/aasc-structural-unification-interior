import KGRealSmearingShear
import SchwartzFourierConjugation
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon
open SchwartzOperations

theorem exists_mass_gap_cutoff (a : Parameters) :
    ∃ χ : 𝓢(ℝ,ℂ),χ 0=1 ∧ ∀ t,2*a.mass*a.speed≤t → χ t=0 := by
  have hgap : (0 : ℝ)<2*a.mass*a.speed:=by
    have hm:=a.mass_pos
    have hc:=a.speed_pos
    positivity
  obtain ⟨b,hsupp,hcompact,hsmooth,_,hb⟩:=exists_contDiff_tsupport_subset (n:=⊤)
    (isOpen_Iio.mem_nhds (show (0 : ℝ)∈Set.Iio (2*a.mass*a.speed) from hgap))
  let χ : 𝓢(ℝ,ℂ):=(hcompact.comp_left (g:=Complex.ofReal) (by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hsmooth)
  refine ⟨χ,by simpa [χ] using congrArg Complex.ofReal hb,?_⟩
  intro t ht
  have hz : b t=0 := by
    by_contra hn
    exact (not_lt_of_ge ht) (hsupp (subset_closure hn))
  simpa [χ,hz]

def massGapCutoff (a : Parameters) : 𝓢(ℝ,ℂ):=Classical.choose (exists_mass_gap_cutoff a)

theorem massGapCutoff_zero (a : Parameters) : massGapCutoff a 0=1 :=
  (Classical.choose_spec (exists_mass_gap_cutoff a)).1

theorem massGapCutoff_vanishes (a : Parameters) (t : ℝ) (ht : 2*a.mass*a.speed≤t) :
    massGapCutoff a t=0 := (Classical.choose_spec (exists_mass_gap_cutoff a)).2 t ht

def shellFrequencyExtensionCLM (a : Parameters) :
    𝓢(Momentum,ℂ) →L[ℂ] 𝓢(Spacetime,ℂ) :=
  (realSmearingShearPullback a).comp (tensorLeftCLM (massGapCutoff a))

theorem shellFrequencyExtension_shell (a : Parameters) (f : 𝓢(Momentum,ℂ)) (p : Momentum) :
    shellFrequencyExtensionCLM a f (shellFrequency a p)=f p := by
  change massGapCutoff a (realSmearingShear a (shellFrequency a p)).1*
    f (realSmearingShear a (shellFrequency a p)).2=f p
  rw [realSmearingShear_shell]
  simp only [massGapCutoff_zero,one_mul]

theorem shellFrequencyExtension_reflected_shell (a : Parameters) (f : 𝓢(Momentum,ℂ)) (p : Momentum) :
    shellFrequencyExtensionCLM a f (-shellFrequency a p)=0 := by
  change massGapCutoff a (realSmearingShear a (-shellFrequency a p)).1*
    f (realSmearingShear a (-shellFrequency a p)).2=0
  rw [realSmearingShear_reflected_shell]
  rw [massGapCutoff_vanishes a _ (realSmearingShear_reflected_gap a p),zero_mul]

def complexSpacetimeLiftCLM (a : Parameters) :
    𝓢(Momentum,ℂ) →L[ℂ] 𝓢(Spacetime,ℂ) :=
  (FourierTransform.fourierInvCLM ℂ 𝓢(Spacetime,ℂ)).comp (shellFrequencyExtensionCLM a)

/-- An actual continuous real-linear lift into the original spacetime Schwartz
space. Realification has no factor 1/2: the reflected shell was proved zero. -/
def realSpacetimeLiftCLM (a : Parameters) : 𝓢(Momentum,ℂ) →L[ℝ] 𝓢(Spacetime,ℂ) :=
  (complexSpacetimeLiftCLM a).restrictScalars ℝ+
    conjugateSchwartzCLM.comp ((complexSpacetimeLiftCLM a).restrictScalars ℝ)

theorem realSpacetimeLift_real (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    conjugateSchwartzCLM (realSpacetimeLiftCLM a f)=realSpacetimeLiftCLM a f := by
  change conjugateSchwartzCLM (complexSpacetimeLiftCLM a f+
    conjugateSchwartzCLM (complexSpacetimeLiftCLM a f))=_
  rw [conjugateSchwartz_add,conjugateSchwartz_involutive]
  exact add_comm _ _

theorem realSpacetimeLift_smearing (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    spacetimeSmearingCLM a (realSpacetimeLiftCLM a f)=f := by
  ext p
  change ((FourierTransform.fourierCLM ℂ 𝓢(Spacetime,ℂ))
    (complexSpacetimeLiftCLM a f+conjugateSchwartzCLM (complexSpacetimeLiftCLM a f)))
    (shellFrequency a p)=f p
  rw [map_add]
  change (𝓕 (complexSpacetimeLiftCLM a f)) (shellFrequency a p)+
    (𝓕 (conjugateSchwartzCLM (complexSpacetimeLiftCLM a f))) (shellFrequency a p)=f p
  rw [fourier_conjugateSchwartz_apply]
  change (𝓕 (𝓕⁻ (shellFrequencyExtensionCLM a f))) (shellFrequency a p)+
    star ((𝓕 (𝓕⁻ (shellFrequencyExtensionCLM a f))) (-shellFrequency a p))=f p
  rw [FourierTransform.fourier_fourierInv_eq,shellFrequencyExtension_shell,
    shellFrequencyExtension_reflected_shell,star_zero,add_zero]

theorem original_real_spacetime_smearing_surjective (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    ∃ h : 𝓢(Spacetime,ℂ),conjugateSchwartzCLM h=h ∧ spacetimeSmearingCLM a h=f :=
  ⟨realSpacetimeLiftCLM a f,realSpacetimeLift_real a f,realSpacetimeLift_smearing a f⟩

end AASCKleinGordon
