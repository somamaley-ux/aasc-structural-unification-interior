import OSRRestNetwork
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR

def lorentzGamma (beta : ℝ) : ℝ := (Real.sqrt (1-beta^2))⁻¹

theorem gamma_positive_and_hyperbolic (beta : ℝ) (subluminal : beta^2 < 1) :
    0 < lorentzGamma beta ∧ (lorentzGamma beta)^2-(lorentzGamma beta*beta)^2=1 := by
  have positive : 0 < 1-beta^2 := sub_pos.mpr subluminal
  have rootPositive := Real.sqrt_pos.mpr positive
  have square := Real.sq_sqrt positive.le
  refine ⟨inv_pos.mpr rootPositive,?_⟩
  unfold lorentzGamma
  field_simp
  nlinarith

def measurementBoost (beta : ℝ) (subluminal : beta^2 < 1) : SRMatrixFrame :=
  srUnitAxialBoost (lorentzGamma beta) (lorentzGamma beta*beta)
    (gamma_positive_and_hyperbolic beta subluminal).2

theorem measurement_boost_actually_supplied (beta : ℝ) (subluminal : beta^2 < 1) :
    measurementBoost beta subluminal ∈ srNativeFrameComparisons :=
  sr_all_future_unit_axial_boosts_are_actually_supplied _ _
    (gamma_positive_and_hyperbolic beta subluminal).2 (gamma_positive_and_hyperbolic beta subluminal).1

theorem axial_boost_spatial_components (t r : ℝ) (hyper : t^2-r^2=1) (z : SREvent) :
    (srMatrixFrameEventLinear (srUnitAxialBoost t r hyper) z).2 0=r*z.1+t*z.2 0 ∧
    (srMatrixFrameEventLinear (srUnitAxialBoost t r hyper) z).2 1=z.2 1 ∧
    (srMatrixFrameEventLinear (srUnitAxialBoost t r hyper) z).2 2=z.2 2 := by
  have coordinates := sr_event_frame_coordinate_square (srUnitAxialBoost t r hyper) z
  have c1 := congrArg (fun v : CoordinatePoint => v 1) coordinates
  have c2 := congrArg (fun v : CoordinatePoint => v 2) coordinates
  have c3 := congrArg (fun v : CoordinatePoint => v 3) coordinates
  constructor
  · simpa [srEventCoordinates,srUnitAxialBoost,srScaledAxialBoostUnit,srScaledAxialBoost,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using c1
  · constructor
    · simpa [srEventCoordinates,srUnitAxialBoost,srScaledAxialBoostUnit,srScaledAxialBoost,
        Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using c2
    · simpa [srEventCoordinates,srUnitAxialBoost,srScaledAxialBoostUnit,srScaledAxialBoost,
        Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using c3

def selectedRestTime (t r : ℝ) (b : SREvent) (T : ℝ) (X : SRSpace) : ℝ :=
  (T-b.1-r*X 0)/t

def selectedEndpoint (t r : ℝ) (hyper : t^2-r^2=1) (b : SREvent) (T : ℝ) (X : SRSpace) : SREvent :=
  frameEvent (srUnitAxialBoost t r hyper) b (selectedRestTime t r b T X,X)

theorem endpoint_selection_is_simultaneous_and_unique (t r : ℝ) (hyper : t^2-r^2=1)
    (positive : 0 < t) (b : SREvent) (T : ℝ) (X : SRSpace) :
    (selectedEndpoint t r hyper b T X).1=T ∧
    ∀ u : ℝ, (frameEvent (srUnitAxialBoost t r hyper) b (u,X)).1=T → u=selectedRestTime t r b T X := by
  constructor
  · change (srMatrixFrameEventLinear (srUnitAxialBoost t r hyper) (selectedRestTime t r b T X,X)).1+b.1=T
    rw [sr_unit_axial_boost_time]
    dsimp [selectedRestTime]
    field_simp
    ring
  · intro u time
    change (srMatrixFrameEventLinear (srUnitAxialBoost t r hyper) (u,X)).1+b.1=T at time
    rw [sr_unit_axial_boost_time] at time
    dsimp [selectedRestTime]
    apply (eq_div_iff positive.ne').mpr
    linarith

theorem actual_selected_endpoint_separation (t r : ℝ) (hyper : t^2-r^2=1)
    (positive : 0 < t) (b : SREvent) (T : ℝ) (X Y : SRSpace) :
    let delta := (selectedEndpoint t r hyper b T Y).2-(selectedEndpoint t r hyper b T X).2
    delta 0=(Y 0-X 0)/t ∧ delta 1=Y 1-X 1 ∧ delta 2=Y 2-X 2 ∧
    selectedRestTime t r b T Y-selectedRestTime t r b T X=-(r/t)*(Y 0-X 0) := by
  have componentsX := axial_boost_spatial_components t r hyper (selectedRestTime t r b T X,X)
  have componentsY := axial_boost_spatial_components t r hyper (selectedRestTime t r b T Y,Y)
  dsimp only
  dsimp only [selectedEndpoint,frameEvent,Prod.snd_add]
  simp only [PiLp.sub_apply,PiLp.add_apply,componentsX.1,componentsY.1,componentsX.2.1,componentsY.2.1,
    componentsX.2.2,componentsY.2.2]
  refine ⟨?_,by ring,by ring,?_⟩
  · dsimp [selectedRestTime]
    field_simp
    nlinarith [congrArg (fun z : ℝ => z*(Y 0-X 0)) hyper]
  · dsimp [selectedRestTime]
    ring

theorem actual_selected_length_squared (t r : ℝ) (hyper : t^2-r^2=1)
    (positive : 0 < t) (b : SREvent) (T : ℝ) (X Y : SRSpace) :
    ‖(selectedEndpoint t r hyper b T Y).2-(selectedEndpoint t r hyper b T X).2‖^2=
      (Y 0-X 0)^2/t^2+(Y 1-X 1)^2+(Y 2-X 2)^2 := by
  have components := actual_selected_endpoint_separation t r hyper positive b T X Y
  simp only [PiLp.sub_apply] at components
  rw [EuclideanSpace.norm_sq_eq]
  norm_num [Fin.sum_univ_succ,Real.norm_eq_abs]
  rw [components.1,components.2.1,components.2.2.1]
  rw [div_pow]
  ring

theorem measurement_selected_rest_time_gap (beta : ℝ) (subluminal : beta^2 < 1)
    (b : SREvent) (T : ℝ) (X Y : SRSpace) :
    selectedRestTime (lorentzGamma beta) (lorentzGamma beta*beta) b T Y-
      selectedRestTime (lorentzGamma beta) (lorentzGamma beta*beta) b T X=-beta*(Y 0-X 0) := by
  have result := (actual_selected_endpoint_separation _ _ (gamma_positive_and_hyperbolic beta subluminal).2
    (gamma_positive_and_hyperbolic beta subluminal).1 b T X Y).2.2.2
  simpa [(gamma_positive_and_hyperbolic beta subluminal).1.ne'] using result

theorem fixed_event_pair_passive_simultaneity (t r : ℝ) (hyper : t^2-r^2=1)
    (p q : SREvent) (simultaneous : p.1=q.1) :
    (srMatrixFrameEventLinear (srUnitAxialBoost t (-r) (by nlinarith)) q).1-
      (srMatrixFrameEventLinear (srUnitAxialBoost t (-r) (by nlinarith)) p).1=-r*(q.2 0-p.2 0) := by
  rw [sr_unit_axial_boost_time,sr_unit_axial_boost_time,simultaneous]
  ring

theorem same_bearer_ticks_actual_dilation (mu0 : ℝ) {n : ℕ} (S : SiteData n) (i : Fin (n+1))
    (positiveMass : 0 < mu0+S.internalEnergy i) (t r : ℝ) (hyper : t^2-r^2=1)
    (b : SREvent) (u v : ℝ) :
    (frameEvent (srUnitAxialBoost t r hyper) b (srMarkedClockEvent mu0 (siteRecord mu0 S i) v)).1-
      (frameEvent (srUnitAxialBoost t r hyper) b (srMarkedClockEvent mu0 (siteRecord mu0 S i) u)).1=
    t*((srNativeCoastingMarkedRecord mu0 (siteRecord mu0 S i) v).2.reading-
      (srNativeCoastingMarkedRecord mu0 (siteRecord mu0 S i) u).2.reading) := by
  rw [site_actual_event mu0 S i positiveMass,site_actual_event mu0 S i positiveMass,
    site_actual_reading mu0 S i positiveMass,site_actual_reading mu0 S i positiveMass]
  simp only [frameEvent,Prod.fst_add,sr_unit_axial_boost_time]
  ring

theorem actual_orientation_preserves_measured_length (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (x y : SRSpace) : ‖Q y-Q x‖=‖y-x‖ := by
  rw [←map_sub,Q.norm_map]

def physicalEvent (c : ℝ) (p : SREvent) : SREvent := (c*p.1,p.2)
def physicalDuration (c : ℝ) (w : SREvent) : ℝ := restLength (physicalEvent c w)/c

theorem physical_time_adapter_inverse (c : ℝ) (positive : 0 < c) (p : SREvent) :
    ((physicalEvent c p).1/c,(physicalEvent c p).2)=p := by
  apply Prod.ext
  · dsimp [physicalEvent]
    field_simp
  · rfl

end AASCKleinGordon.OperationalSR
