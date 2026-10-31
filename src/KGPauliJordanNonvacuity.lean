import KGCommutatorCorrelationSupport

noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

theorem shellFrequency_time_negative (a : Parameters) (p : Momentum) : shellFrequency a p 0<0 := by
  rw [shellFrequency_apply]
  change fourierWaveScale a*(-energy a p/a.speed)<0
  exact mul_neg_of_pos_of_neg (fourierWaveScale_pos a)
    (div_neg_of_neg_of_pos (neg_neg_of_pos (energy_pos a p)) a.speed_pos)

theorem exists_nonzero_massShellCommutator_test (a : Parameters) :
    ∃ h : 𝓢(Spacetime,ℂ),massShellCommutatorCLM a h≠0 := by
  have ho : IsOpen {q : Spacetime | q 0<0} := isOpen_lt (by fun_prop) continuous_const
  obtain ⟨b,hsupp,hcompact,hsmooth,hbounds,hb⟩ :=
    exists_contDiff_tsupport_subset (n:=⊤) (ho.mem_nhds (shellFrequency_time_negative a 0))
  let G : 𝓢(Spacetime,ℂ) :=
    (hcompact.comp_left (g:=Complex.ofReal) (by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hsmooth)
  let g : 𝓢(Momentum,ℂ) := shellRestrictionCLM a G
  have hi : Integrable (fun p => b (shellFrequency a p)) (wignerMeasure a) := by
    have h := (g.integrable (μ:=wignerMeasure a)).re
    change Integrable (fun p => ((b (shellFrequency a p) : ℂ)).re) (wignerMeasure a) at h
    simpa only [Complex.ofReal_re] using h
  have hp : 0<∫ p,b (shellFrequency a p) ∂wignerMeasure a := by
    apply integral_pos_of_integrable_nonneg_nonzero
      (hsmooth.continuous.comp (shellFrequency_temperate a).1.continuous) hi
      (fun p => (hbounds (Set.mem_range_self _)).1) (x:=0)
    change b (shellFrequency a 0)≠0
    rw [hb]
    norm_num
  have hn (p : Momentum) : G (-shellFrequency a p)=0 := by
    change (b (-shellFrequency a p) : ℂ)=0
    apply Complex.ofReal_eq_zero.mpr
    by_contra he
    have hm := hsupp (subset_closure he)
    change (-shellFrequency a p) 0<0 at hm
    simp only [PiLp.neg_apply] at hm
    linarith [shellFrequency_time_negative a p]
  refine ⟨𝓕⁻ G,?_⟩
  rw [massShellCommutator_apply,FourierTransform.fourier_fourierInv_eq]
  have hni : (∫ p,G (-shellFrequency a p) ∂wignerMeasure a)=0 := by
    simp only [hn,integral_zero]
  rw [hni,sub_zero]
  intro hz
  have hr := congrArg Complex.re hz
  change RCLike.re (∫ p,g p ∂wignerMeasure a)=0 at hr
  rw [← integral_re (g.integrable (μ:=wignerMeasure a))] at hr
  change (∫ p,b (shellFrequency a p) ∂wignerMeasure a)=0 at hr
  exact hp.ne' hr

theorem massShellCommutator_nonzero (a : Parameters) : massShellCommutatorCLM a≠0 := by
  obtain ⟨h,hh⟩ := exists_nonzero_massShellCommutator_test a
  intro he
  apply hh
  rw [he]
  rfl

end AASCKleinGordon
