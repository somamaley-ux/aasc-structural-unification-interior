import KGGeneralLorentzCoreAttachment
import KGProperLorentzTopology
import KGParticleAdjointness
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped SchwartzMap Topology
namespace AASCKleinGordon

theorem particleLorentz_parameter_continuous (a : Parameters) (n : ℕ)
    (x : ParticleConfiguration n) : Continuous (fun L : ProperLorentzTransform => particleLorentzME a n L x) := by
  change Continuous (fun L => fun i => lorentzShellMap a L (x i))
  exact continuous_pi (fun i => lorentzShellMap_parameter_continuous a (x i))

theorem particleLorentz_schwartz_inner_continuous (a : Parameters) (n : ℕ)
    (H K : 𝓢(ParticleConfiguration n,ℂ)) :
    Continuous (fun L : ProperLorentzTransform => inner ℂ
      (particleLorentzUnitary a n L (particleSchwartzToHilbert a n H))
      (particleSchwartzToHilbert a n K)) := by
  have he (L : ProperLorentzTransform) : inner ℂ
      (particleLorentzUnitary a n L (particleSchwartzToHilbert a n H))
      (particleSchwartzToHilbert a n K) =
      ∫ x,star (H (particleLorentzME a n L⁻¹ x))*K x ∂particleMeasure a n := by
    rw [particleLorentz_intertwines_schwartz,particle_schwartz_inner_eq]
    rfl
  simp_rw [he]
  apply continuous_iff_continuousAt.mpr
  intro M
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => SchwartzMap.seminorm ℝ 0 0 H*‖K x‖)
  · exact Eventually.of_forall (fun L =>
      (((H.continuous.comp (particleLorentzMap_temperate a n L⁻¹).1.continuous).star).mul
        K.continuous).aestronglyMeasurable)
  · exact Eventually.of_forall (fun L => Eventually.of_forall (fun x => by
      rw [norm_mul,norm_star]
      exact mul_le_mul_of_nonneg_right (H.norm_le_seminorm ℝ _) (norm_nonneg _)))
  · exact (K.integrable (μ:=particleMeasure a n)).norm.const_mul _
  · exact Eventually.of_forall (fun x =>
      (((H.continuous.comp ((particleLorentz_parameter_continuous a n x).comp continuous_inv)).star).mul
        continuous_const).tendsto M)

end AASCKleinGordon
