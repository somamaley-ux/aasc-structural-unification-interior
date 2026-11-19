import OccupiedMetricProfiles
import OriginalEHGeometricCore
import LocalMetricJetCongruence
import OccupiedMetricGerms

/-! Full compact variation profiles distinguish natural responses that depend on the
metric germ. The candidate need not be given by an action or have a prescribed
differential order. The reference action and its constants are fixed. -/

namespace AASCOccupiedProfiles
noncomputable section
open AASCSemanticExhaustion AASCProjectionObservations AASCKleinGordon
open TopologicalSpace Filter
open scoped Topology ContDiff
set_option autoImplicit false

/-- The output at a smooth Lorentz point depends only on the local metric. -/
def SmoothMetricGermLocal (E : MetricFieldResponse) : Prop :=
  ∀ g h p, C2LorentzMetricAt g p → C2LorentzMetricAt h p →
    (∀ i j, ContDiffAt ℝ ∞ (fun x => g x i j) p) →
    (∀ i j, ContDiffAt ℝ ∞ (fun x => h x i j) p) →
    g =ᶠ[𝓝 p] h → E g p = E h p

/-- Only changes from a smooth metric to an affine Lorentz frame at the
point are needed to transport the comparison. -/
def SmoothFrameResponseNatural (E : MetricFieldResponse) : Prop :=
  ∀ (g : MetricField) (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint),
    MetricFieldSymmetric g → SmoothCoordinateMetric g → LorentzFrameAt g p B →
    E (framedMetricField g p B) 0 =
      (coordinateFrameMatrix B).transpose * E g p * coordinateFrameMatrix B

theorem smooth_frame_natural_of_regular (E : MetricFieldResponse)
    (natural : RegularLorentzResponseNatural E) : SmoothFrameResponseNatural E := by
  intro g p B sym sm frame
  have dom : C2LorentzMetricAt g p :=
    ⟨sym, fun i j => ((sm i j).contDiffAt).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)), B, frame⟩
  have der : HasFDerivAt (affineCoordinateMap p B) B.toContinuousLinearMap 0 :=
    quadraticCoordinateMap_hasFDerivAt_zero p B _
  have cov := natural (affineCoordinateMap p B) 0 B (affineCoordinateMap_smooth p B).contDiffAt
    der g (by simpa only [affineCoordinateMap_zero] using dom)
  simpa only [framedMetricField, affineCoordinateMap_zero, affineCoordinateMap_jacobian] using cov

/-- At a genuinely occupied operand, full compact profiles determine every
component of a continuous symmetric covariant response. -/
theorem full_readings_identify_occupied_response {Ω : Opens CoordinatePoint}
    (E : MetricFieldResponse) (κ Λ : ℝ) (hk : κ ≠ 0) (H : AdmittedOperand Ω)
    (cont : ∀ i j, ContinuousOn (fun x => E (originalEHActMetric H.1) x i j)
      (Ω : Set CoordinatePoint))
    (sym : ∀ x ∈ Ω, ∀ i j, E (originalEHActMetric H.1) x i j = E (originalEHActMetric H.1) x j i)
    (same : MatchesCompactReadings κ Λ H.1 (sourceDensityCoordinates
      (raisedSourceTensorDensity (originalEHActMetric H.1) (E (originalEHActMetric H.1)))))
    (p : CoordinatePoint) (hp : p ∈ Ω) :
    E (originalEHActMetric H.1) p = originalEHGeometricResponse κ Λ (originalEHActMetric H.1) p := by
  rw [eh_original_geometric_tensor_identified κ Λ hk _ p
    (original_eh_act_metric_negative H.1 H.2 p)]
  exact covariant_einstein_of_compact_metric_readings κ Λ hk H.1 H.2 _ cont sym same p hp

/-- If a germ-local covariant response agrees with *all* occupied compact
variation readings, it agrees with the action-derived response at every
smooth metric with a Lorentz frame at the point. The cutoff copies a whole
germ, so there is no upper derivative order in the hypotheses on the rival. -/
theorem germ_local_response_eq_eh_of_all_occupied_profiles
    (Ω : Opens CoordinatePoint) (hΩ : (0 : CoordinatePoint) ∈ Ω)
    (E : MetricFieldResponse) (κ Λ : ℝ) (hk : κ ≠ 0)
    (locality : SmoothMetricGermLocal E) (natural : SmoothFrameResponseNatural E)
    (cont : ∀ (H : AdmittedOperand Ω) i j, ContinuousOn
      (fun x => E (originalEHActMetric H.1) x i j) (Ω : Set CoordinatePoint))
    (sym : ∀ (H : AdmittedOperand Ω) x, x ∈ Ω →
      ∀ i j, E (originalEHActMetric H.1) x i j = E (originalEHActMetric H.1) x j i)
    (profiles : ∀ H : AdmittedOperand Ω, MatchesCompactReadings κ Λ H.1
      (sourceDensityCoordinates (raisedSourceTensorDensity (originalEHActMetric H.1)
        (E (originalEHActMetric H.1)))))
    (g : MetricField) (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (sg : MetricFieldSymmetric g) (smooth : SmoothCoordinateMetric g)
    (frame : LorentzFrameAt g p B) : E g p = originalEHGeometricResponse κ Λ g p := by
  obtain ⟨H, equal⟩ := exists_admitted_operand_eq_framed_germ Ω hΩ g p B sg smooth frame
  let F := framedMetricField g p B
  have smoothH := original_eh_act_metric_smooth H.1
  have domH := original_eh_act_metric_lorentz H.1 H.2 0
  have smoothF (i j) : ContDiffAt ℝ ∞ (fun x => F x i j) 0 := by
    apply (smoothH i j).contDiffAt.congr_of_eventuallyEq
    exact equal.symm.mono fun _ h => congrArg (fun M : Tensor2 => M i j) h
  have domF : C2LorentzMetricAt F 0 := c2_lorentz_of_normal_value F
    (framedMetricField_symmetric g p B sg) (fun i j => (smoothF i j).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) (framedMetricField_value g p B frame)
  have rivalAt := locality _ F 0 domH domF (fun i j => (smoothH i j).contDiffAt) smoothF equal
  have ehAt := eh_original_geometric_response_twojet_local κ Λ hk _ F 0 domH domF
    (metric_twojet_of_eventuallyEq _ _ _ equal)
  have occupied := full_readings_identify_occupied_response E κ Λ hk H
    (cont H) (sym H) (profiles H) 0 hΩ
  have framed : E F 0 = originalEHGeometricResponse κ Λ F 0 :=
    rivalAt.symm.trans (occupied.trans ehAt)
  have ehNatural := smooth_frame_natural_of_regular _
    (eh_original_geometric_response_regular_natural κ Λ hk)
  exact frame_matrix_pullback_injective B
    ((natural g p B sg smooth frame).symm.trans (framed.trans (ehNatural g p B sg smooth frame)))

/-- A disagreement at an arbitrary smooth, framed point is witnessed by an
actual one-component compact variation at an occupied bounded operand. -/
theorem different_germ_has_occupied_compact_test
    (Ω : Opens CoordinatePoint) (hΩ : (0 : CoordinatePoint) ∈ Ω)
    (E : MetricFieldResponse) (κ Λ : ℝ) (hk : κ ≠ 0)
    (locality : SmoothMetricGermLocal E) (natural : SmoothFrameResponseNatural E)
    (cont : ∀ (H : AdmittedOperand Ω) i j, ContinuousOn
      (fun x => E (originalEHActMetric H.1) x i j) (Ω : Set CoordinatePoint))
    (sym : ∀ (H : AdmittedOperand Ω) x, x ∈ Ω →
      ∀ i j, E (originalEHActMetric H.1) x i j = E (originalEHActMetric H.1) x j i)
    (g : MetricField) (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (sg : MetricFieldSymmetric g) (smooth : SmoothCoordinateMetric g) (frame : LorentzFrameAt g p B)
    (differs : E g p ≠ originalEHGeometricResponse κ Λ g p) :
    ∃ (H : AdmittedOperand Ω) (i : Fin 10) (φ : ScalarSourceProbe Ω),
      (∫ x, sourceDensityCoordinates (raisedSourceTensorDensity (originalEHActMetric H.1)
          (E (originalEHActMetric H.1))) i x * φ x) ≠
        (2 / symmetricSourceWeight i) * deriv (fun t : ℝ =>
          originalEHRelativeAction κ Λ wickNativeFlatMetric (H.1 + t • sourceTestInsertion i φ)) 0 := by
  classical
  by_contra! agrees
  apply differs
  exact germ_local_response_eq_eh_of_all_occupied_profiles Ω hΩ E κ Λ hk locality natural cont
    sym agrees g p B sg smooth frame

/-- The target coefficients need only be smooth on an open chart about the
point. A global smooth representative is constructed; the original input and
the reference action are identified there by agreement on a neighborhood. -/
theorem original_profiles_determine_eh_on_smooth_chart
    (Ω : Opens CoordinatePoint) (hΩ : (0 : CoordinatePoint) ∈ Ω)
    (E : MetricFieldResponse) (κ Λ : ℝ) (hk : κ ≠ 0)
    (locality : SmoothMetricGermLocal E) (natural : SmoothFrameResponseNatural E)
    (cont : ∀ (H : AdmittedOperand Ω) i j, ContinuousOn
      (fun x => E (originalEHActMetric H.1) x i j) (Ω : Set CoordinatePoint))
    (sym : ∀ (H : AdmittedOperand Ω) x, x ∈ Ω →
      ∀ i j, E (originalEHActMetric H.1) x i j = E (originalEHActMetric H.1) x j i)
    (profiles : ∀ H : AdmittedOperand Ω, MatchesCompactReadings κ Λ H.1
      (sourceDensityCoordinates (raisedSourceTensorDensity (originalEHActMetric H.1)
        (E (originalEHActMetric H.1)))))
    (V : Opens CoordinatePoint) (p : CoordinatePoint) (hp : p ∈ V)
    (g : MetricField) (sg : MetricFieldSymmetric g)
    (reg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) (V : Set CoordinatePoint))
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (frame : LorentzFrameAt g p B) :
    E g p = originalEHGeometricResponse κ Λ g p := by
  obtain ⟨h, hs, hreg, equal⟩ := exists_smooth_symmetric_field_eq_germ_on_open V p hp g sg reg
  have hframe : LorentzFrameAt h p B := by
    unfold LorentzFrameAt at frame ⊢
    rwa [equal.eq_of_nhds]
  have gAt i j := (reg i j).contDiffAt (V.isOpen.mem_nhds hp)
  have finite : (2 : WithTop ℕ∞) ≤ (∞) := WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)
  have dg : C2LorentzMetricAt g p := ⟨sg, fun i j => (gAt i j).of_le finite, B, frame⟩
  have dh : C2LorentzMetricAt h p := ⟨hs, fun i j => (hreg i j).contDiffAt.of_le finite, B, hframe⟩
  have atH := germ_local_response_eq_eh_of_all_occupied_profiles Ω hΩ E κ Λ hk locality natural
    cont sym profiles h p B hs hreg hframe
  exact (locality h g p dh dg (fun i j => (hreg i j).contDiffAt) gAt equal).symm.trans
    (atH.trans (eh_original_geometric_response_twojet_local κ Λ hk h g p dh dg
      (metric_twojet_of_eventuallyEq h g p equal)))

end
end AASCOccupiedProfiles
