import OSRMeasuringFrameSelection

/-! A measuring frame is retained relative to the original coasting congruence.
Its ambient hyperplane is transported with the presentation; changing the
relative measuring frame is a distinct measurement question. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR

structure MeasuringQuery where
  frame : SRMatrixFrame
  origin : SREvent
  time : ℝ

def measuringSiteTime (Q : MeasuringQuery) (X : SRSpace) : ℝ :=
  selectedSiteTime Q.frame Q.origin Q.time X

def measuringHyperplane (Q : MeasuringQuery) : Set SREvent :=
  {p | (frameEvent Q.frame Q.origin p).1=Q.time}

def presentedMeasuringHyperplane (A : SRMatrixFrame) (b : SREvent) (Q : MeasuringQuery) : Set SREvent :=
  frameEvent A b '' measuringHyperplane Q

theorem same_measuring_hyperplane_is_actually_transported (A B : SRMatrixFrame) (b c : SREvent) (Q : MeasuringQuery) :
    presentedMeasuringHyperplane (B*A) (frameEvent B c b) Q=
      frameEvent B c '' presentedMeasuringHyperplane A b Q := by
  unfold presentedMeasuringHyperplane
  rw [Set.image_image]
  congr 1
  funext p
  exact (frame_event_composition B A c b p).symm

theorem measured_endpoint_lies_on_retained_hyperplane (Q : MeasuringQuery)
    (admitted : Q.frame ∈ srNativeFrameComparisons) (X : SRSpace) :
    ((measuringSiteTime Q X,X):SREvent) ∈ measuringHyperplane Q :=
  (measuring_frame_selected_events_actual_and_unique Q.frame admitted Q.origin Q.time X).1

theorem presented_selected_event_transport (A B : SRMatrixFrame) (b c : SREvent)
    (Q : MeasuringQuery) (X : SRSpace) :
    frameEvent (B*A) (frameEvent B c b) (measuringSiteTime Q X,X)=
      frameEvent B c (frameEvent A b (measuringSiteTime Q X,X)) :=
  (frame_event_composition B A c b _).symm

end AASCKleinGordon.OperationalSR
