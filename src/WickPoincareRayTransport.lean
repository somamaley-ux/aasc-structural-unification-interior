import WickPoincareProtocolTransport

noncomputable section
set_option maxHeartbeats 1500000
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem wick_unit_representative_poincare (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (u : FiniteParticleCore) :
    originalWickUnitRepresentative a (corePoincare a b L u)=
      corePoincare a b L (originalWickUnitRepresentative a u) := by
  have norm : ‖finiteParticleCoreToFock a (corePoincare a b L u)‖=‖finiteParticleCoreToFock a u‖ := by
    rw [← fockPoincare_intertwines_original_core]
    exact (fockPoincareUnitary a b L).norm_map _
  unfold originalWickUnitRepresentative
  rw [norm,map_smul]

def wickPoincareNonzeroCore (a : Parameters) (b : Spacetime) (L : ProperLorentzTransform)
    (u : WickNonzeroCore) : WickNonzeroCore :=
  ⟨corePoincare a b L u.val,by
    intro zero
    apply u.property
    apply (corePoincareEquiv a b L).injective
    change corePoincare a b L u.val=corePoincare a b L 0
    simpa only [map_zero] using zero⟩

def wickPoincareRayAction (a : Parameters) (b : Spacetime) (L : ProperLorentzTransform) :
    Quotient wickCoreRaySetoid → Quotient wickCoreRaySetoid :=
  Quotient.map (wickPoincareNonzeroCore a b L) (by
    intro u v same
    obtain ⟨z,nonzero,identity⟩ := same
    refine ⟨z,nonzero,?_⟩
    exact (congrArg (corePoincare a b L) identity).trans ((corePoincare a b L).map_smul z u.val))

theorem wick_transported_chart_phase (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    (z : ℂ) (unit : ‖z‖=1) (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) (π : WickKGOriginalProtocol (wickAffineMetricRegion b L Ω)) :
    wickKGTransportedChartOutput a s (z • u) b L Ω π=
      wickKGTransportedChartOutput a s u b L Ω π := by
  classical
  cases π with
  | first δ =>
    exact congrArg WickKGOriginalReadout.first
      (wick_KG_original_first_output_unit_phase a s z unit u δ)
  | finite J =>
    by_cases inside : J∈wickTransportedMetricDomain b L Ω
    · simp only [wickKGTransportedChartOutput, if_pos inside]
      exact congrArg WickKGOriginalReadout.finite
        (congrArg Complex.re (wick_original_finite_action_unit_phase a s z unit u u J))
    · simp only [wickKGTransportedChartOutput, if_neg inside]

theorem wick_transported_normalized_prequotient_family (a : Parameters) (s : ℝ)
    (b : Spacetime) (L : ProperLorentzTransform) (Ω : Opens CoordinatePoint)
    (u v : WickNonzeroCore) (same : wickCoreRaySetoid.r u v)
    (π : WickKGOriginalProtocol (wickAffineMetricRegion b L Ω)) :
    wickKGTransportedChartOutput a s (originalWickUnitRepresentative a u.val) b L Ω π=
      wickKGTransportedChartOutput a s (originalWickUnitRepresentative a v.val) b L Ω π := by
  have sameUnit : wickCoreRaySetoid.r (originalWickUnitNonzeroRepresentative a u)
      (originalWickUnitNonzeroRepresentative a v) :=
    Quotient.exact ((original_wick_unit_representative_same_ray a u).trans
      ((Quotient.sound same).trans (original_wick_unit_representative_same_ray a v).symm))
  obtain ⟨z,_,identity⟩ := sameUnit
  change originalWickUnitRepresentative a v.val=z • originalWickUnitRepresentative a u.val at identity
  have normalized : ‖finiteParticleCoreToFock a
      (z • originalWickUnitRepresentative a u.val)‖=1 := by
    rw [← identity]
    exact original_wick_unit_representative_norm a v.val v.property
  have unit : ‖z‖=1 := by
    simpa only [map_smul,norm_smul,original_wick_unit_representative_norm a u.val u.property,
      mul_one] using normalized
  change wickKGTransportedChartOutput a s (originalWickUnitRepresentative a u.val) b L Ω π=
    wickKGTransportedChartOutput a s (originalWickUnitRepresentative a v.val) b L Ω π
  rw [identity]
  exact (wick_transported_chart_phase a s _ z unit b L Ω π).symm

/-- Fix the whole normalized prequotient family before descending it. -/
def wickKGTransportedRayOutput (a : Parameters) (s : ℝ) (b : Spacetime)
    (L : ProperLorentzTransform) (Ω : Opens CoordinatePoint) :
    Quotient wickCoreRaySetoid → WickKGOriginalProtocol (wickAffineMetricRegion b L Ω) →
      WickKGOriginalReadout :=
  Quotient.lift (fun u => wickKGTransportedChartOutput a s (originalWickUnitRepresentative a u.val) b L Ω)
    (by intro u v same; funext π
        exact wick_transported_normalized_prequotient_family a s b L Ω u v same π)

theorem wick_KG_entire_ray_family_poincare (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (Ω : Opens CoordinatePoint)
    (ray : Quotient wickCoreRaySetoid) (π : WickKGOriginalProtocol Ω) :
    wickKGTransportedRayOutput a s b L Ω (wickPoincareRayAction a b L ray)
      (wickKGProtocolPoincare b L π)=wickKGOriginalRayOutput a s Ω ray π := by
  refine Quotient.inductionOn ray (fun u => ?_)
  change wickKGTransportedChartOutput a s (originalWickUnitRepresentative a (corePoincare a b L u.val))
    b L Ω (wickKGProtocolPoincare b L π)=wickKGOriginalOutput a s (originalWickUnitRepresentative a u.val) π
  rw [wick_unit_representative_poincare]
  exact wick_KG_all_readouts_poincare a b L s (originalWickUnitRepresentative a u.val) Ω π

theorem wick_original_ray_source_poincare (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (Ω : Opens CoordinatePoint)
    (ray : Quotient wickCoreRaySetoid) (H : MetricSourceProbe Ω) :
    originalWickRayMetricResponse a s (wickAffineMetricRegion b L Ω)
      (wickPoincareRayAction a b L ray) (wickNativeAffineMetricTest b L H)=
      originalWickRayMetricResponse a s Ω ray H := by
  refine Quotient.inductionOn ray (fun u => ?_)
  rw [show wickPoincareRayAction a b L (Quotient.mk wickCoreRaySetoid u)=
      Quotient.mk wickCoreRaySetoid (wickPoincareNonzeroCore a b L u) from rfl]
  have transformed := congrArg
    (fun f : MetricSourceProbe (wickAffineMetricRegion b L Ω) →L[ℝ] ℝ =>
      f (wickNativeAffineMetricTest b L H))
    (original_wick_ray_source_is_actual_unit_response a s
      (wickAffineMetricRegion b L Ω) (wickPoincareNonzeroCore a b L u))
  have original := congrArg (fun f : MetricSourceProbe Ω →L[ℝ] ℝ => f H)
    (original_wick_ray_source_is_actual_unit_response a s Ω u)
  have response := wick_original_native_response_poincare a b L s
    (originalWickUnitRepresentative a u.val) Ω H
  have value : (wickPoincareNonzeroCore a b L u).val=corePoincare a b L u.val := rfl
  have unitIdentity := (congrArg (originalWickUnitRepresentative a) value).trans
    (wick_unit_representative_poincare a b L u.val)
  have normalization := congrArg
    (fun v : FiniteParticleCore => originalWickNativeRealMetricResponse a s v
      (wickAffineMetricRegion b L Ω) (wickNativeAffineMetricTest b L H))
    unitIdentity
  calc
    _ = originalWickNativeRealMetricResponse a s
        (originalWickUnitRepresentative a (wickPoincareNonzeroCore a b L u).val)
        (wickAffineMetricRegion b L Ω) (wickNativeAffineMetricTest b L H) := transformed
    _ = originalWickNativeRealMetricResponse a s
        (corePoincare a b L (originalWickUnitRepresentative a u.val))
        (wickAffineMetricRegion b L Ω) (wickNativeAffineMetricTest b L H) := normalization
    _ = originalWickNativeRealMetricResponse a s
        (originalWickUnitRepresentative a u.val) Ω H := response
    _ = _ := original.symm

end AASCKleinGordon
