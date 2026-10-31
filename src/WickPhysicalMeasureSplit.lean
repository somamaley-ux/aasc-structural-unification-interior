import WickWignerWeightSchwartz
import KGParticleProductTransport

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory
namespace AASCKleinGordon

theorem wick_particle_integral_head (a : Parameters) (n : ℕ)
    (f : ParticleConfiguration (n+1) → ℂ) (hf : Integrable f (particleMeasure a (n+1))) :
    (∫ z,f z ∂particleMeasure a (n+1))=
      ∫ p,∫ r,f (Fin.cons p r) ∂particleMeasure a n ∂wignerMeasure a := by
  have transformed := (joinParticleCoordinates_measurePreserving a n).integral_comp
    (joinParticleCoordinates n).toHomeomorph.measurableEmbedding f
  have hi := ((joinParticleCoordinates_measurePreserving a n).integrable_comp_emb
    (joinParticleCoordinates n).toHomeomorph.measurableEmbedding).mpr hf
  exact transformed.symm.trans (integral_prod _ hi)

theorem wick_particle_integral_two_visible (a : Parameters) (n : ℕ)
    (f : ParticleConfiguration (n+2) → ℂ) (hf : Integrable f (particleMeasure a (n+2))) :
    (∫ z,f z ∂particleMeasure a (n+2))=
      ∫ p,∫ q,∫ r,f (Fin.cons p (Fin.cons q r))
        ∂particleMeasure a n ∂wignerMeasure a ∂wignerMeasure a := by
  rw [wick_particle_integral_head a (n+1) f hf]
  have hi := ((joinParticleCoordinates_measurePreserving a (n+1)).integrable_comp_emb
    (joinParticleCoordinates (n+1)).toHomeomorph.measurableEmbedding).mpr hf
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with p hp
  exact wick_particle_integral_head a n (fun r => f (Fin.cons p r)) hp

theorem wick_two_wigner_integrals_weighted_volume (a : Parameters) (f : Momentum → Momentum → ℂ) :
    (∫ p,∫ q,f p q ∂wignerMeasure a ∂wignerMeasure a)=
      ∫ p,∫ q,(wignerWeight a p : ℂ)*(wignerWeight a q : ℂ)*f p q := by
  rw [wigner_integral_eq_weighted_volume]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => by
    dsimp only
    rw [wigner_integral_eq_weighted_volume,← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun q => by ring))

theorem wick_momentum_euclidean_inverse_volume : MeasurePreserving momentumEuclidean.symm :=
  PiLp.volume_preserving_ofLp (Fin 3)

theorem wick_momentum_integral_euclidean (f : Momentum → ℂ) :
    (∫ p,f p)=∫ p : WickSpaceSlice,f (momentumEuclidean.symm p) :=
  (wick_momentum_euclidean_inverse_volume.integral_comp
    momentumEuclidean.symm.toHomeomorph.measurableEmbedding f).symm

theorem wick_momentum_pair_integral_euclidean (f : Momentum → Momentum → ℂ) :
    (∫ p,∫ q,f p q)=∫ p : WickSpaceSlice,∫ q : WickSpaceSlice,
      f (momentumEuclidean.symm p) (momentumEuclidean.symm q) := by
  rw [wick_momentum_integral_euclidean]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => wick_momentum_integral_euclidean _)

end AASCKleinGordon
