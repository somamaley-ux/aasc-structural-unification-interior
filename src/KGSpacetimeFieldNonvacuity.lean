import KGSpacetimeFieldCore
import SchwartzFourierConjugation
import KGCoreCCR
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

noncomputable section
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon
open SchwartzOperations

theorem shellFrequency_zero_nonzero (a : Parameters) : shellFrequency a 0 ≠ 0 := by
  have hc : shellCovector a 0 ≠ 0 := by
    intro h
    have he := congrArg (fun x : Spacetime => (fourCoordinateJoin.symm x).1) h
    rw [shellCovector_eq_join] at he
    change (fourCoordinateJoin.symm
      (fourCoordinateJoin (-energy a 0/a.speed, 0))).1 =
        (fourCoordinateJoin.symm 0).1 at he
    simp only [ContinuousLinearEquiv.symm_apply_apply, map_zero] at he
    change -energy a 0/a.speed = 0 at he
    have hp := div_pos (energy_pos a 0) a.speed_pos
    rw [neg_div] at he
    exact hp.ne' (neg_eq_zero.mp he)
  exact smul_ne_zero (fourierWaveScale_pos a).ne' hc

theorem exists_real_spacetime_test_nonzero_shell (a : Parameters) :
    ∃ h : 𝓢(Spacetime,ℂ), conjugateSchwartzCLM h = h ∧ spacetimeSmearingCLM a h 0 = (1/2 : ℂ) := by
  let ξ := shellFrequency a 0
  have hξ : ξ ≠ -ξ := by
    intro he
    have hz : (2 : ℝ) • ξ = 0 := by
      rw [two_smul]
      calc ξ + ξ = (-ξ) + ξ := congrArg (fun x => x + ξ) he
        _ = 0 := neg_add_cancel ξ
    exact shellFrequency_zero_nonzero a ((smul_eq_zero.mp hz).resolve_left (by norm_num))
  have hn : ({-ξ}ᶜ : Set Spacetime) ∈ nhds ξ :=
    isClosed_singleton.isOpen_compl.mem_nhds (by simpa using hξ)
  obtain ⟨b, hsupp, hcompact, hsmooth, _, hb⟩ :=
    exists_contDiff_tsupport_subset (n:=⊤) hn
  have hbneg : b (-ξ) = 0 := by
    by_contra he
    have hm : -ξ ∈ Function.support b := he
    exact (hsupp (subset_closure hm)) (by simp)
  let G : 𝓢(Spacetime,ℂ) :=
    (hcompact.comp_left (g:=Complex.ofReal) (by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hsmooth)
  have hG : G ξ = 1 := by simpa [G] using congrArg Complex.ofReal hb
  have hGn : G (-ξ) = 0 := by simpa [G] using congrArg Complex.ofReal hbneg
  let H : 𝓢(Spacetime,ℂ) := 𝓕⁻ G
  have hF : 𝓕 H = G := FourierTransform.fourier_fourierInv_eq G
  refine ⟨(1/2 : ℂ) • (H + conjugateSchwartzCLM H), ?_, ?_⟩
  · rw [conjugateSchwartz_smul, conjugateSchwartz_add, conjugateSchwartz_involutive]
    simp [add_comm]
  · rw [map_smul, map_add]
    change (1/2 : ℂ) * ((𝓕 H) ξ + (𝓕 (conjugateSchwartzCLM H)) ξ) = 1/2
    rw [fourier_conjugateSchwartz_apply, hF, hG, hGn]
    simp

theorem exists_real_field_vacuum_excitation (a : Parameters) (s : ℝ) (hs : s ≠ 0) :
    ∃ h : 𝓢(Spacetime,ℂ), conjugateSchwartzCLM h = h ∧ spacetimeFieldCore a s h vacuumCore ≠ 0 := by
  obtain ⟨h, hr, hk⟩ := exists_real_spacetime_test_nonzero_shell a
  refine ⟨h, hr, ?_⟩
  have hn : spacetimeSmearingCLM a h ≠ 0 := by
    intro hz
    have he := congrArg (fun f : 𝓢(Momentum,ℂ) => f 0) hz
    change spacetimeSmearingCLM a h 0 = 0 at he
    rw [hk] at he
    norm_num at he
  simp only [spacetimeFieldCore, LinearMap.smul_apply, LinearMap.add_apply,
    annihilationCore_vacuum_zero, add_zero]
  exact smul_ne_zero (Complex.ofReal_ne_zero.mpr hs) (creationCore_vacuum_nonzero _ hn)

end AASCKleinGordon
