import KGAxisBoostGroup
import KGParticleAdjointness
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
open scoped SchwartzMap Topology
namespace AASCKleinGordon

theorem axisBoostMomentum_rapidity_continuous (a : Parameters) (p : Momentum) :
    Continuous (fun r => axisBoostMomentum a r p) := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun r => Real.sinh r*(energy a p/a.speed)+Real.cosh r*p 0)
    fun_prop
  · change Continuous (fun _ : ℝ => p 1)
    exact continuous_const
  · change Continuous (fun _ : ℝ => p 2)
    exact continuous_const

theorem particleAxisBoost_rapidity_continuous (a : Parameters) (n : ℕ)
    (x : ParticleConfiguration n) : Continuous (fun r => particleAxisBoostME a n r x) := by
  change Continuous (fun r => fun i => axisBoostMomentum a r (x i))
  exact continuous_pi (fun i => axisBoostMomentum_rapidity_continuous a (x i))

theorem particleAxisBoost_schwartz_inner_continuous (a : Parameters) (n : ℕ)
    (H K : 𝓢(ParticleConfiguration n,ℂ)) :
    Continuous (fun r => inner ℂ
      (particleAxisBoostUnitary a n r (particleSchwartzToHilbert a n H))
      (particleSchwartzToHilbert a n K)) := by
  have he (r : ℝ) : inner ℂ
      (particleAxisBoostUnitary a n r (particleSchwartzToHilbert a n H))
      (particleSchwartzToHilbert a n K) =
      ∫ x,star (H (particleAxisBoostME a n (-r) x))*K x ∂particleMeasure a n := by
    rw [particleAxisBoost_intertwines_schwartz,particle_schwartz_inner_eq]
    rfl
  simp_rw [he]
  apply continuous_iff_continuousAt.mpr
  intro s
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => SchwartzMap.seminorm ℝ 0 0 H*‖K x‖)
  · exact Eventually.of_forall (fun r =>
      (((H.continuous.comp (particleAxisBoost_temperate a n (-r)).1.continuous).star).mul
        K.continuous).aestronglyMeasurable)
  · exact Eventually.of_forall (fun r => Eventually.of_forall (fun x => by
      rw [norm_mul,norm_star]
      exact mul_le_mul_of_nonneg_right (H.norm_le_seminorm ℝ _) (norm_nonneg _)))
  · exact (K.integrable (μ:=particleMeasure a n)).norm.const_mul _
  · exact Eventually.of_forall (fun x =>
      (((H.continuous.comp ((particleAxisBoost_rapidity_continuous a n x).comp continuous_neg)).star).mul
        continuous_const).tendsto s)

end AASCKleinGordon
