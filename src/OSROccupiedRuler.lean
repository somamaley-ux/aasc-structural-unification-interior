import OSRNetworkPopulation
import OSRPopulatedProtocol
import OSRMeasurementSourceClosure

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
open Set AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR
open KGQuantum W9 TopologicalSpace AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

theorem every_nonzero_endpoint_standard_has_actual_radar_and_measuring_use
    (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint)
    (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega})
    (X Y : SRSpace) (distinct : Y ≠ X) (phaseX phaseY : ℝ)
    (Q : MeasuringQuery) (admitted : Q.frame ∈ srNativeFrameComparisons) :
    ∃ d : NetworkData a s Omega 1, networkSound a s Omega 1 d ∧
      d.sites.position 0=X ∧ d.sites.position 1=Y ∧
      ∃ radar measurement, radarRead a s Omega 1 d 0 0=some radar ∧
        radar.length=‖Y-X‖ ∧ measuringRead a s Omega 1 d Q 0 1=some measurement := by
  let sites : Fin 2 → SRSpace := fun i => if i=0 then X else Y
  let phase : Fin 2 → ℝ := fun i => if i=0 then phaseX else phaseY
  let u := measuringSiteTime Q X
  let v := measuringSiteTime Q Y
  let lo := min u v
  let hi := max (max u v) (lo+2*‖Y-X‖)
  let request : ExchangeRequest 1 := ⟨0,1,lo,0,1⟩
  let d := populatedNetworkData a s Omega 1 r H sites phase lo hi [request]
  have ordered : lo ≤ hi := (min_le_left u v).trans ((le_max_left u v).trans (le_max_left _ _))
  have sound := populated_network_actual_sound a s Omega 1 r H sites phase lo hi ordered [request]
  have radarDomain : requestDomain a s Omega 1 d 0 0 := by
    apply populated_network_every_declared_valid_request_is_executed a s Omega 1 r H sites phase lo hi [request] 0 request
    · rfl
    · simpa [sites] using distinct
    · norm_num [request]
    · norm_num [request]
    · exact le_refl _
    · change lo + 2 * ‖Y-X‖ + 0 ≤ max (max u v) (lo+2*‖Y-X‖)
      simpa only [add_zero] using le_max_right (max u v) (lo+2*‖Y-X‖)
  have domain : measuringDomain a s Omega 1 d Q 0 1 := by
    refine ⟨admitted,rfl,rfl,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [d,populatedNetworkData,sites] using distinct
    · exact min_le_left u v
    · exact (le_max_left u v).trans (le_max_left _ _)
    · exact min_le_right u v
    · exact (le_max_right u v).trans (le_max_left _ _)
    · intro t ht
      trivial
    · intro t ht
      trivial
  refine ⟨d,sound,by simp [d,populatedNetworkData,sites],by simp [d,populatedNetworkData,sites],
    actualRadarAnswer a s Omega 1 d 0 request,actualMeasuringAnswer a s Omega 1 d Q 0 1,?_,?_,?_⟩
  · rw [radarRead,if_pos radarDomain]
    rfl
  · simpa [d,populatedNetworkData,sites,request] using (occupied_network_radar_answer a s Omega 1 d sound 0 request).2
  · simp [measuringRead,domain]

end AASCKleinGordon.OperationalSR
