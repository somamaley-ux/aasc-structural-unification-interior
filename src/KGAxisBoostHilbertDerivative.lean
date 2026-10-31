import KGAxisBoostDifferential
import DenseWeakDerivative

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
open scoped SchwartzMap Topology
namespace AASCKleinGordon

theorem particleAxisBoost_weak_hasDerivAt (a : Parameters) (n : ℕ)
    (H K : 𝓢(ParticleConfiguration n,ℂ)) (r : ℝ) :
    HasDerivAt (fun s => inner ℂ (particleSchwartzToHilbert a n K)
      (particleAxisBoostUnitary a n s (particleSchwartzToHilbert a n H)))
      (inner ℂ (particleSchwartzToHilbert a n K)
        (particleAxisBoostUnitary a n r (particleSchwartzToHilbert a n
          (particleAxisBoostDifferential a n H)))) r := by
  have he (H : 𝓢(ParticleConfiguration n,ℂ)) (s : ℝ) :
      inner ℂ (particleSchwartzToHilbert a n K)
        (particleAxisBoostUnitary a n s (particleSchwartzToHilbert a n H)) =
        ∫ x,star (K x)*H (particleAxisBoostME a n (-s) x) ∂particleMeasure a n := by
    rw [particleAxisBoost_intertwines_schwartz,particle_schwartz_inner_eq]
    rfl
  simp_rw [he]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=particleMeasure a n) (s:=Set.univ) (x₀:=r)
    (F:=fun s x => star (K x)*H (particleAxisBoostME a n (-s) x))
    (F':=fun s x => star (K x)*particleAxisBoostDifferential a n H (particleAxisBoostME a n (-s) x))
    (bound:=fun x => ‖K x‖*SchwartzMap.seminorm ℝ 0 0 (particleAxisBoostDifferential a n H))
    univ_mem ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall (fun s =>
      (K.continuous.star.mul (H.continuous.comp
        (particleAxisBoost_temperate a n (-s)).1.continuous)).aestronglyMeasurable)
  · exact schwartz_pair_integrable _ K (particleAxisBoostSchwartzCLM a n r H)
  · exact (K.continuous.star.mul ((particleAxisBoostDifferential a n H).continuous.comp
      (particleAxisBoost_temperate a n (-r)).1.continuous)).aestronglyMeasurable
  · exact Eventually.of_forall (fun x s _ => by
      rw [norm_mul,norm_star]
      exact mul_le_mul_of_nonneg_left ((particleAxisBoostDifferential a n H).norm_le_seminorm ℝ _)
        (norm_nonneg _))
  · exact (K.integrable (μ:=particleMeasure a n)).norm.mul_const _
  · exact Eventually.of_forall (fun x s _ =>
      (particleAxisBoost_schwartz_pointwise_hasDerivAt a n H x s).const_mul (star (K x)))

theorem particleAxisBoost_schwartz_hasDerivAt (a : Parameters) (n : ℕ)
    (H : 𝓢(ParticleConfiguration n,ℂ)) (r : ℝ) :
    HasDerivAt (fun s => particleAxisBoostUnitary a n s (particleSchwartzToHilbert a n H))
      (particleAxisBoostUnitary a n r (particleSchwartzToHilbert a n
        (particleAxisBoostDifferential a n H))) r :=
  hasDerivAt_of_dense_inner_derivative (particleSchwartzToHilbert a n)
    (particleSchwartzToHilbert_dense a n) _ _
    (particleAxisBoost_strongly_continuous a n _)
    (fun K r => particleAxisBoost_weak_hasDerivAt a n H K r) r

theorem particleAxisBoost_schwartz_hasDerivAt_zero (a : Parameters) (n : ℕ)
    (H : 𝓢(ParticleConfiguration n,ℂ)) :
    HasDerivAt (fun s => particleAxisBoostUnitary a n s (particleSchwartzToHilbert a n H))
      (particleSchwartzToHilbert a n (particleAxisBoostDifferential a n H)) 0 := by
  simpa only [particleAxisBoostUnitary_zero] using particleAxisBoost_schwartz_hasDerivAt a n H 0

end AASCKleinGordon
