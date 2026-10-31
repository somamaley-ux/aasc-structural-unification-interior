import KGOriginalWickActionVariation
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Actual compact metric paths are nondegenerate uniformly near zero, and
their relative quantum action integrands are integrable. -/
noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory Filter Set
open scoped Topology
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem wick_compact_metric_path_nondegenerate (H : Spacetime → NativeRealMatrix)
    (hH : Continuous H) (hcomp : HasCompactSupport H) :
    ∀ᶠ t : ℝ in 𝓝 0,∀ x,(wickFlatMetric+t • H x).det ≠ 0 := by
  let K : Set Spacetime := tsupport H
  have hK : IsCompact K := hcomp
  let G : ℝ × Spacetime → NativeRealMatrix := fun z => wickFlatMetric+z.1 • H z.2
  have hG : Continuous G := continuous_const.add (continuous_fst.smul (hH.comp continuous_snd))
  let Udet : Set (ℝ × Spacetime) := {z | (G z).det ≠ 0}
  have hUdet : IsOpen Udet := isOpen_ne.preimage hG.matrix_det
  have hprod : ({0} : Set ℝ) ×ˢ K ⊆ Udet := by
    rintro ⟨t,x⟩ ⟨ht,_⟩
    have ht0 : t=0 := ht
    subst t
    simp [Udet,G,wick_flat_metric_det]
  obtain ⟨U,V,hU,hV,hzero,hall,hUV⟩ := generalized_tube_lemma
    (isCompact_singleton (x := (0 : ℝ))) hK hUdet hprod
  have hz : (0 : ℝ) ∈ U := hzero (by simp)
  filter_upwards [hU.mem_nhds hz] with t ht x
  by_cases hx : x ∈ K
  · exact hUV (show (t,x) ∈ U ×ˢ V from ⟨ht,hall hx⟩)
  · have hzero : H x=0 := image_eq_zero_of_notMem_tsupport hx
    simp [hzero,wick_flat_metric_det]

theorem original_wick_relative_density_hasCompactSupport (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (H : Spacetime → NativeRealMatrix)
    (hcomp : HasCompactSupport H) (t : ℝ) :
    HasCompactSupport (fun x => wickQuantumActionDensity (wickFlatMetric+t • H x)
      (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x)-
      wickQuantumActionDensity wickFlatMetric
        (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x)) := by
  apply hcomp.mono
  intro x hx
  by_contra hzero
  have hz : H x=0 := by simpa only [Function.mem_support,not_not] using hzero
  simpa [Function.mem_support,hz] using hx

theorem original_wick_relative_action_integrable_near_zero (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (H : Spacetime → NativeRealMatrix)
    (hH : Continuous H) (hcomp : HasCompactSupport H) :
    ∀ᶠ t : ℝ in 𝓝 0,Integrable (fun x => wickQuantumActionDensity (wickFlatMetric+t • H x)
      (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x)-
      wickQuantumActionDensity wickFlatMetric
        (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x)) := by
  filter_upwards [wick_compact_metric_path_nondegenerate H hH hcomp] with t ht
  have hgt : Continuous (fun x => wickFlatMetric+t • H x) := continuous_const.add (continuous_const.smul hH)
  have hD := original_wick_derivative_components_continuous a s u v
  have hM := original_wick_mass_square_continuous a s u v
  have hn : wickFlatMetric.det ≠ 0 := by rw [wick_flat_metric_det]; norm_num
  have hf : Continuous (fun x => wickQuantumActionDensity (wickFlatMetric+t • H x)
      (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x)-
      wickQuantumActionDensity wickFlatMetric
        (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x)) :=
    continuous_iff_continuousAt.2 (fun x =>
      (wick_quantum_density_continuousAt _ _ _ hgt.continuousAt hD.continuousAt hM.continuousAt (ht x)).sub
      (wick_quantum_density_continuousAt _ _ _ continuousAt_const hD.continuousAt hM.continuousAt hn))
  exact hf.integrable_of_hasCompactSupport (original_wick_relative_density_hasCompactSupport a s u v H hcomp t)

end AASCKleinGordon
