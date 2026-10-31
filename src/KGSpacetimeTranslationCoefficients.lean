import KGSpacetimeAxisBoost
import KGAxisBoostClosedDomain
import KGFockTranslationGroups
import KGFockTranslationVacuum

noncomputable section
open scoped BigOperators
namespace AASCKleinGordon

def eventMomentumPair (a : Parameters) (b : Spacetime) (p : Momentum) : ℝ :=
  inner ℝ b (shellCovector a p)

theorem eventMomentumPair_coordinates (a : Parameters) (b : Spacetime) (p : Momentum) :
    eventMomentumPair a b p= -b 0*energy a p/a.speed+∑ j : Fin 3,b j.succ*p j := by
  rw [eventMomentumPair,shellCovector_eq_join]
  simp [PiLp.inner_apply,RCLike.inner_apply,Fin.sum_univ_succ,fourCoordinateJoin,fourCoordinateCons]
  ring

theorem eventMomentumPair_continuous (a : Parameters) (b : Spacetime) : Continuous (eventMomentumPair a b) :=
  continuous_const.inner ((shellCovector_temperate a).1.continuous)

theorem eventMomentumPair_add (a : Parameters) (b d : Spacetime) (p : Momentum) :
    eventMomentumPair a (b+d) p=eventMomentumPair a b p+eventMomentumPair a d p :=
  inner_add_left _ _ _

theorem eventMomentumPair_zero (a : Parameters) (p : Momentum) : eventMomentumPair a 0 p=0 :=
  inner_zero_left _

theorem eventMomentumPair_boost (a : Parameters) (r : ℝ) (b : Spacetime) (p : Momentum) :
    eventMomentumPair a b (axisBoostMomentum a (-r) p)=
      eventMomentumPair a (spacetimeAxisBoostCLE r b) p := by
  unfold eventMomentumPair
  rw [shellCovector_axisBoost,← spacetimeAxisBoost_transpose]

def particleEventMomentum (a : Parameters) (n : ℕ) (b : Spacetime) (x : ParticleConfiguration n) : ℝ :=
  ∑ i,eventMomentumPair a b (x i)

theorem particleEventMomentum_continuous (a : Parameters) (n : ℕ) (b : Spacetime) :
    Continuous (particleEventMomentum a n b) := by
  apply continuous_finset_sum
  intro i _
  exact (eventMomentumPair_continuous a b).comp (continuous_apply i)

theorem particleEventMomentum_permutation (a : Parameters) (n : ℕ) (b : Spacetime)
    (σ : Equiv.Perm (Fin n)) (x : ParticleConfiguration n) :
    particleEventMomentum a n b (particlePermutation n σ x)=particleEventMomentum a n b x := by
  unfold particleEventMomentum
  simp only [particlePermutation_apply]
  exact Equiv.sum_comp σ.symm (fun i : Fin n => eventMomentumPair a b (x i))

theorem particleEventMomentum_add (a : Parameters) (n : ℕ) (b d : Spacetime) (x : ParticleConfiguration n) :
    particleEventMomentum a n (b+d) x=particleEventMomentum a n b x+particleEventMomentum a n d x := by
  simp only [particleEventMomentum,eventMomentumPair_add,Finset.sum_add_distrib]

theorem particleEventMomentum_zero (a : Parameters) (n : ℕ) (x : ParticleConfiguration n) :
    particleEventMomentum a n 0 x=0 := by simp [particleEventMomentum,eventMomentumPair_zero]

theorem particleEventMomentum_boost (a : Parameters) (n : ℕ) (r : ℝ) (b : Spacetime)
    (x : ParticleConfiguration n) :
    particleEventMomentum a n b (particleAxisBoostME a n (-r) x)=
      particleEventMomentum a n (spacetimeAxisBoostCLE r b) x := by
  apply Finset.sum_congr rfl
  intro i _
  exact eventMomentumPair_boost a r b (x i)

def timeTranslationEvent (a : Parameters) (t : ℝ) : Spacetime := timeInjection (-a.speed*t)
def spatialTranslationEvent (j : Fin 3) (s : ℝ) : Spacetime := spatialInjection (Pi.single j s)

theorem eventMomentumPair_time (a : Parameters) (t : ℝ) (p : Momentum) :
    eventMomentumPair a (timeTranslationEvent a t) p=t*energy a p := by
  rw [eventMomentumPair_coordinates]
  simp [timeTranslationEvent,timeInjection,fourCoordinateJoin,fourCoordinateCons]
  field_simp [a.speed_pos.ne']

theorem eventMomentumPair_spatial (a : Parameters) (j : Fin 3) (s : ℝ) (p : Momentum) :
    eventMomentumPair a (spatialTranslationEvent j s) p=s*p j := by
  rw [eventMomentumPair_coordinates]
  fin_cases j <;> simp [spatialTranslationEvent,spatialInjection,fourCoordinateJoin,fourCoordinateCons,Pi.single_apply]

end AASCKleinGordon
