import KGSpacetimeTranslationUnitary
import KGJointMomentumCone

noncomputable section
set_option maxHeartbeats 1400000
namespace AASCKleinGordon

theorem wick_original_event_pair_contravariant (a : Parameters) (b : Spacetime) (p : Momentum) :
    eventMomentumPair a b p= -b 0*massShell a p 0+
      ∑ j : Fin 3,b j.succ*massShell a p j.succ := by
  have spatial : ∀ j : Fin 3,massShell a p j.succ=p j := by intro j; fin_cases j <;> rfl
  rw [eventMomentumPair_coordinates]
  simp_rw [spatial]
  change -b 0*energy a p/a.speed+_= -b 0*(energy a p/a.speed)+_
  ring

theorem wick_original_particle_event_contravariant (a : Parameters) (n : ℕ)
    (b : Spacetime) (z : ParticleConfiguration n) :
    particleEventMomentum a n b z= -b 0*particleFourMomentum a n z 0+
      ∑ j : Fin 3,b j.succ*particleFourMomentum a n z j.succ := by
  unfold particleEventMomentum
  simp_rw [wick_original_event_pair_contravariant]
  simp only [particleFourMomentum,Finset.sum_apply,Finset.mul_sum,Finset.sum_add_distrib]
  rw [Finset.sum_comm]

theorem wick_original_time_event_coordinate (a : Parameters) (t : ℝ) :
    timeTranslationEvent a t 0= -a.speed*t := rfl

theorem wick_original_time_event_same_group (a : Parameters) (t : ℝ) (v : FockHilbert a) :
    fockEventTranslation a (timeTranslationEvent a t) v=fockTimeTranslation a t v :=
  fockEventTranslation_time a t v

theorem wick_original_spatial_event_same_group (a : Parameters) (j : Fin 3)
    (t : ℝ) (v : FockHilbert a) :
    fockEventTranslation a (spatialTranslationEvent j t) v=fockSpatialTranslation a j t v :=
  fockEventTranslation_spatial a j t v

end AASCKleinGordon
