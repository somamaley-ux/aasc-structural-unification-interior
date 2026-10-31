import OSROccupiedRelay
import OSRInertialMeasurements

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR

theorem positive_speed_beta_is_subluminal (c v : ℝ) (speed : 0 < c) (velocity : v^2 < c^2) : (v/c)^2 < 1 := by
  rw [div_pow]
  exact (div_lt_one (sq_pos_of_pos speed)).mpr velocity

theorem physical_rest_duration_is_actual_time (c t : ℝ) (speed : 0 < c) (forward : 0 ≤ t) :
    physicalDuration c (t,0)=t := by
  unfold physicalDuration physicalEvent restLength
  rw [sr_original_order_quadratic_computed]
  norm_num only [norm_zero]
  rw [sub_zero,Real.sqrt_sq (mul_nonneg speed.le forward),mul_div_cancel_left₀ t speed.ne']

theorem actual_directional_clock_readings_in_physical_units (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (x : SRSpace) (phase c t u : ℝ) (speed : 0 < c) :
    ((srNativeClockCoastFlow mu0 (c*u*U.1) (directionalClock mu0 J U x phase)).reading-
      (srNativeClockCoastFlow mu0 (c*t*U.1) (directionalClock mu0 J U x phase)).reading)/c=u-t := by
  rw [directional_clock_actual_reading mu0 J positive U unit x phase (c*u),
    directional_clock_actual_reading mu0 J positive U unit x phase (c*t)]
  field_simp
  ring

theorem occupied_radar_physical_units (mu0 : ℝ) {n : ℕ} (S : SiteData n) (i j : Fin (n+1))
    (positive_i : 0 < mu0+S.internalEnergy i) (positive_j : 0 < mu0+S.internalEnergy j)
    (emit delay energy c : ℝ) (speed : 0 < c) :
    let R := relayAtSites S i j emit delay energy
    (siteReading mu0 S j (relayRelease R).1-siteReading mu0 S j (relayArrival R).1)/c=delay/c ∧
    c*((siteReading mu0 S i (relayReturn R).1-siteReading mu0 S i (relayDeparture R).1)/c-delay/c)/2=R.length ∧
    (siteReading mu0 S i (relayReturn R).1-siteReading mu0 S i (relayDeparture R).1)/c=(2*R.length+delay)/c := by
  dsimp only
  have actual := occupied_radar_readings mu0 S i j positive_i positive_j emit delay energy
  refine ⟨congrArg (fun r : ℝ => r/c) actual.2.1,?_,?_⟩
  · field_simp
    nlinarith [actual.2.2]
  · apply congrArg (fun r : ℝ => r/c)
    linarith [actual.2.2]

theorem actual_tick_dilation_in_physical_time (mu0 : ℝ) {n : ℕ} (S : SiteData n) (i : Fin (n+1))
    (positive : 0 < mu0+S.internalEnergy i) (beta : ℝ) (subluminal : beta^2 < 1)
    (b : SREvent) (u v c : ℝ) (speed : 0 < c) :
    ((frameEvent (measurementBoost beta subluminal) b (srMarkedClockEvent mu0 (siteRecord mu0 S i) v)).1-
      (frameEvent (measurementBoost beta subluminal) b (srMarkedClockEvent mu0 (siteRecord mu0 S i) u)).1)/c=
    lorentzGamma beta*((siteReading mu0 S i v-siteReading mu0 S i u)/c) := by
  have actual := same_bearer_ticks_actual_dilation mu0 S i positive (lorentzGamma beta) (lorentzGamma beta*beta)
    (gamma_positive_and_hyperbolic beta subluminal).2 b u v
  change _/c=lorentzGamma beta*(_/c)
  rw [show measurementBoost beta subluminal=srUnitAxialBoost (lorentzGamma beta) (lorentzGamma beta*beta)
    (gamma_positive_and_hyperbolic beta subluminal).2 from rfl,actual]
  unfold siteReading
  ring

end AASCKleinGordon.OperationalSR
