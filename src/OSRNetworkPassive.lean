import OSRNetworkEvolution

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
open Set AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR
open KGQuantum W9 TopologicalSpace AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
variable (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint) (n : ℕ)

def passiveNetworkData (B : SRMatrixFrame) (c : SREvent) (d : NetworkData a s Omega n) : NetworkData a s Omega n :=
  {d with frame := B*d.frame,origin := frameEvent B c d.origin,region := frameEvent B c '' d.region}

def passiveNetwork (B : SRMatrixFrame) (c : SREvent) (x : NetworkSource a s Omega n) : NetworkSource a s Omega n :=
  {x with data := passiveNetworkData a s Omega n B c x.data}

theorem passive_network_actually_sound (B : SRMatrixFrame) (admitted : B ∈ srNativeFrameComparisons)
    (c : SREvent) (d : NetworkData a s Omega n) (sound : networkSound a s Omega n d) :
    networkSound a s Omega n (passiveNetworkData a s Omega n B c d) :=
  ⟨sound.1,srNativeFrameComparisons.mul_mem admitted sound.2.1,sound.2.2⟩

theorem inverse_chart_after_actual_presentation (A B : SRMatrixFrame) (b c p : SREvent) :
    frameInverse (B*A) (frameEvent B c b) (frameEvent B c p)=frameInverse A b p := by
  apply frame_event_injective (B*A) (frameEvent B c b)
  rw [frame_inverse_right,←frame_event_composition,frame_inverse_right]

theorem inverse_chart_domain_image (A B : SRMatrixFrame) (b c : SREvent) (O : Set SREvent) :
    frameInverse (B*A) (frameEvent B c b) '' (frameEvent B c '' O)=frameInverse A b '' O := by
  rw [Set.image_image]
  congr 1
  funext p
  exact inverse_chart_after_actual_presentation A B b c p

theorem passive_network_request_domain (B : SRMatrixFrame) (c : SREvent)
    (d : NetworkData a s Omega n) (index : ℕ) (correction : ℝ) :
    requestDomain a s Omega n (passiveNetworkData a s Omega n B c d) index correction ↔
      requestDomain a s Omega n d index correction := by
  simp only [requestDomain,passiveNetworkData,requestRelay,inverse_chart_domain_image,
    ←frame_event_composition,actual_segment_domain_transport]

theorem passive_network_measuring_domain (B : SRMatrixFrame) (c : SREvent)
    (d : NetworkData a s Omega n) (Q : MeasuringQuery) (i j : Fin (n+1)) :
    measuringDomain a s Omega n (passiveNetworkData a s Omega n B c d) Q i j ↔
      measuringDomain a s Omega n d Q i j := by
  simp only [measuringDomain,passiveNetworkData,←frame_event_composition,actual_segment_domain_transport]

def transportMeasuringAnswer (B : SRMatrixFrame) (c : SREvent) (answer : MeasuringAnswer) : MeasuringAnswer :=
  {answer with firstEvent := frameEvent B c answer.firstEvent,secondEvent := frameEvent B c answer.secondEvent}

theorem actual_measuring_answer_same_question_transport (B : SRMatrixFrame) (c : SREvent)
    (d : NetworkData a s Omega n) (Q : MeasuringQuery) (i j : Fin (n+1)) :
    actualMeasuringAnswer a s Omega n (passiveNetworkData a s Omega n B c d) Q i j=
      transportMeasuringAnswer B c (actualMeasuringAnswer a s Omega n d Q i j) := by
  simp only [actualMeasuringAnswer,passiveNetworkData,transportMeasuringAnswer,frame_event_composition]

theorem measuring_read_same_question_transport_and_failure (B : SRMatrixFrame) (c : SREvent)
    (d : NetworkData a s Omega n) (Q : MeasuringQuery) (i j : Fin (n+1)) :
    measuringRead a s Omega n (passiveNetworkData a s Omega n B c d) Q i j=
      (measuringRead a s Omega n d Q i j).map (transportMeasuringAnswer B c) := by
  simp only [measuringRead,passive_network_measuring_domain]
  split <;> simp [actual_measuring_answer_same_question_transport]

def passiveNetworkOperation (d : NetworkData a s Omega n) : NetworkOperation n → NetworkOperation n
  | .certifyRuler i j T => .certifyMeasuring ⟨d.frame,d.origin,T⟩ i j
  | op => op

theorem network_partial_operation_passive_square (B : SRMatrixFrame) (c : SREvent)
    (op : NetworkOperation n) (x : NetworkSource a s Omega n) :
    networkOperation a s Omega n (passiveNetworkOperation a s Omega n x.data op) (passiveNetwork a s Omega n B c x)=
      (networkOperation a s Omega n op x).map (passiveNetwork a s Omega n B c) := by
  cases op <;>
    simp [passiveNetworkOperation,networkOperation,networkDataOperation,passiveNetwork,passiveNetworkData,
      ←frame_event_composition,actual_segment_domain_transport,inverse_chart_domain_image,requestRelay,
      requestDomain,measuringDomain,rulerDomain,Option.map_map,Function.comp_def]

theorem network_operation_retains_presentation (op : NetworkOperation n)
    (d e : NetworkData a s Omega n) (step : networkDataOperation a s Omega n op d=some e) :
    e.frame=d.frame ∧ e.origin=d.origin := by
  cases op <;> simp only [networkDataOperation] at step
  all_goals first | (cases step; exact ⟨rfl,rfl⟩) |
    (split_ifs at step <;> cases step <;> exact ⟨rfl,rfl⟩)

theorem passive_program_parameter_stable (op : NetworkOperation n) (x y : NetworkSource a s Omega n)
    (step : networkOperation a s Omega n op x=some y) :
    passiveNetworkOperation a s Omega n y.data=passiveNetworkOperation a s Omega n x.data := by
  have square := network_operation_actual_data_square a s Omega n op x
  rw [step,Option.map_some] at square
  have same := network_operation_retains_presentation a s Omega n op x.data y.data square.symm
  funext next
  cases next <;> simp [passiveNetworkOperation,same.1,same.2]

theorem passive_network_finite_first_failure (B : SRMatrixFrame) (c : SREvent)
    (ops : List (NetworkOperation n)) (x : NetworkSource a s Omega n) :
    networkFirstFailure a s Omega n (ops.map (passiveNetworkOperation a s Omega n x.data))
      (passiveNetwork a s Omega n B c x)=networkFirstFailure a s Omega n ops x := by
  induction ops generalizing x with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.map_cons,networkFirstFailure,network_partial_operation_passive_square]
    cases step : networkOperation a s Omega n op x with
    | none => simp [step]
    | some y =>
      simp only [step,Option.map_some]
      rw [←passive_program_parameter_stable a s Omega n op x y step,ih]

end AASCKleinGordon.OperationalSR
