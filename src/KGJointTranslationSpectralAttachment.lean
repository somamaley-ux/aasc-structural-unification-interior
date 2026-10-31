import KGJointSpectralCountable

noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
open scoped Topology BigOperators
namespace AASCKleinGordon

/-- The original Fourier covector pairing of physical contravariant four-momentum. -/
def jointTranslationPair (b : Spacetime) (q : FourMomentum) : ℝ :=
  -b 0*q 0+∑j : Fin 3,b j.succ*q j.succ

theorem particleEventMomentum_eq_jointPair (a : Parameters) (n : ℕ)
    (b : Spacetime) (x : ParticleConfiguration n) :
    particleEventMomentum a n b x=jointTranslationPair b (particleFourMomentum a n x) := by
  simp only [particleEventMomentum,eventMomentumPair_coordinates,jointTranslationPair,
    particleFourMomentum_time,particleFourMomentum_space,Finset.sum_add_distrib]
  congr 1
  · rw [← Finset.sum_div,← Finset.mul_sum,particleTotalEnergy]
    ring
  · rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,totalMomentumCLM_apply]

def jointTranslationSymbol (a : Parameters) (b : Spacetime) : FockContractiveSymbol a where
  value n x:=Translation.phase a.hbar 1 (particleEventMomentum a n b x)
  measurable n:=Multiplication.translationPhase_measurable _
    (particleEventMomentum_continuous a n b).measurable a.hbar 1
  invariant n σ x:=by rw [particleEventMomentum_permutation]
  bound n x:=(Translation.phase_norm _ _ _).le

theorem jointTranslationSymbol_factors_through_fourMomentum (a : Parameters) (b : Spacetime)
    (n : ℕ) (x : ParticleConfiguration n) :
    (jointTranslationSymbol a b).value n x=
      Translation.phase a.hbar 1 (jointTranslationPair b (particleFourMomentum a n x)) := by
  change Translation.phase a.hbar 1 (particleEventMomentum a n b x)=_
  rw [particleEventMomentum_eq_jointPair]

/-- The spectral phase multiplier IS the original translation, on every Fock vector. -/
theorem jointTranslationSymbol_eq_original (a : Parameters) (b : Spacetime) :
    symbolOperator a (jointTranslationSymbol a b)=
      (fockEventTranslation a b).toLinearIsometry.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext n
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [symbolOperator_ae a (jointTranslationSymbol a b) f n,
    Multiplication.phaseMultiplier_ae (particleEventMomentum a n b)
      (particleEventMomentum_continuous a n b).measurable a.hbar 1 (f n).val] with x hx hy
  exact hx.trans hy.symm

/-- Exact Fourier matrix elements of the joint multiplication spectral representation. -/
theorem original_translation_joint_fourier_matrix (a : Parameters) (b : Spacetime)
    (f g : FockHilbert a) :
    inner ℂ f (fockEventTranslation a b g)=∑'n,∫x,
      star ((f n).val x)*
        (Translation.phase a.hbar 1 (jointTranslationPair b (particleFourMomentum a n x))*(g n).val x)
          ∂particleMeasure a n := by
  have he:=congrArg (fun T : FockHilbert a →L[ℂ] FockHilbert a => T g)
    (jointTranslationSymbol_eq_original a b)
  change symbolOperator a (jointTranslationSymbol a b) g=fockEventTranslation a b g at he
  rw [← he]
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  change inner ℂ (f n).val (symbolOperator a (jointTranslationSymbol a b) g n).val=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [symbolOperator_ae a (jointTranslationSymbol a b) g n] with x hx
  rw [hx,jointTranslationSymbol_factors_through_fourMomentum]
  simp only [RCLike.inner_apply,starRingEnd_apply]
  ring

end AASCKleinGordon
