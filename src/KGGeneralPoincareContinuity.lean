import KGGeneralPoincareCovariance
import KGGeneralLorentzStrongContinuity
import KGEventTranslationContinuity

noncomputable section
set_option maxHeartbeats 1600000
namespace AASCKleinGordon

theorem fockEventTranslation_jointly_continuous (a : Parameters) :
    Continuous (fun q : Spacetime × FockHilbert a => fockEventTranslation a q.1 q.2) :=
  continuous_isometric_action_of_orbits (fun b => fockEventTranslation a b)
    (fun b => (fockEventTranslation a b).isometry) (fockEventTranslation_strongly_continuous a)

theorem fockPoincare_strongly_continuous (a : Parameters) (f : FockHilbert a) :
    Continuous (fun q : Spacetime × ProperLorentzTransform => fockPoincareUnitary a q.1 q.2 f) := by
  change Continuous (fun q : Spacetime × ProperLorentzTransform =>
    fockEventTranslation a q.1 (fockLorentzUnitary a q.2 f))
  let Φ : Spacetime × ProperLorentzTransform → Spacetime × FockHilbert a :=
    fun q => (q.1,fockLorentzUnitary a q.2 f)
  have hL : Continuous (fun q : Spacetime × ProperLorentzTransform => fockLorentzUnitary a q.2 f) :=
    (fockLorentz_strongly_continuous a f).comp continuous_snd
  have hΦ : Continuous Φ := (continuous_fst : Continuous
    (fun q : Spacetime × ProperLorentzTransform => q.1)).prodMk hL
  have h := (fockEventTranslation_jointly_continuous a).comp hΦ
  exact h

theorem fockPoincare_jointly_continuous (a : Parameters) :
    Continuous (fun q : (Spacetime × ProperLorentzTransform) × FockHilbert a =>
      fockPoincareUnitary a q.1.1 q.1.2 q.2) :=
  continuous_isometric_action_of_orbits (fun q : Spacetime × ProperLorentzTransform =>
    fockPoincareUnitary a q.1 q.2)
    (fun q => (fockPoincareUnitary a q.1 q.2).isometry) (fockPoincare_strongly_continuous a)

theorem spacetimeLorentz_parameter_continuous (x : Spacetime) :
    Continuous (fun L : ProperLorentzTransform => spacetimeLorentzCLE L x) := by
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.continuous.comp
    (properLorentz_evaluation_continuous (fun i => x i))

theorem spacetimeLorentz_jointly_continuous :
    Continuous (fun q : ProperLorentzTransform × Spacetime => spacetimeLorentzCLE q.1 q.2) := by
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.continuous.comp
    ((properLorentz_forward_continuous.comp continuous_fst).clm_apply
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).continuous.comp continuous_snd))

end AASCKleinGordon
