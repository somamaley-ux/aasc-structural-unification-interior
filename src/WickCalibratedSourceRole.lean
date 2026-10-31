import WickStructuredSourceQuotient
import WickNativeSameTensorCharges

noncomputable section
open TopologicalSpace MeasureTheory
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem wick_role_source_prequotient_coherent (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u : WickNonzeroCore) :
    wickRolePiA a s Ω (wickRoleSx a s Ω (Quotient.mk wickCoreRaySetoid u))=
      wickRolePiA a s Ω (wickOriginalRoleSource a s Ω u) := by
  apply Quotient.sound
  apply wick_full_role_implies_source_agreement
  exact wick_role_same_ray_entire_signature a s Ω _ _
    (Quotient.exact (Quotient.out_eq (Quotient.mk wickCoreRaySetoid u)))

theorem wick_role_source_same_original_ray_response (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (ray : Quotient wickCoreRaySetoid) (H : MetricSourceProbe Ω) :
    (wickRoleSx a s Ω ray).attachment.functional H=originalWickRayMetricResponse a s Ω ray H :=
  wick_native_ray_presentation_same_source a s Ω ray H

theorem wick_role_density_all_test_pairing (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (ray : Quotient wickCoreRaySetoid) (H : MetricSourceProbe Ω) :
    (1/2 : ℝ)*metricSourcePairing (wickRoleQg a s Ω (wickRolePiA a s Ω (wickRoleSx a s Ω ray))) H=
      originalWickRayMetricResponse a s Ω ray H :=
  ((wickRoleSx a s Ω ray).attachment.half_pairing H).trans
    (wick_role_source_same_original_ray_response a s Ω ray H)

theorem wick_role_concrete_density_is_original (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (ray : Quotient wickCoreRaySetoid) :
    wickRoleTA (wickRoleSx a s Ω ray)=representedMetricSource (originalWickRayMetricResponse a s Ω ray) := by
  apply constructed_metric_source_unique
  exact wick_role_density_all_test_pairing a s Ω ray

theorem wick_role_concrete_source_poincare (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (ray : Quotient wickCoreRaySetoid)
    (b : Spacetime) (L : ProperLorentzTransform) :
    wickRoleTA (wickRoleSx a s (wickAffineMetricRegion b L Ω) (wickPoincareRayAction a b L ray))=
      representedMetricSource ((originalWickRayMetricResponse a s Ω ray).comp
        (wickNativeAffineMetricInverseCLM b L Ω)) := by
  rw [wick_role_concrete_density_is_original]
  apply congrArg representedMetricSource
  ext J
  have transport := wick_original_ray_source_poincare a b L s Ω ray
    (wickNativeAffineMetricInverseCLM b L Ω J)
  rw [wick_native_affine_inverse_right] at transport
  exact transport

/-- Actual inertial witness on the same predictive carrier. All fields are
constructed below from the original representation and computed comparisons. -/
structure WickRoleInertialWitness (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (u : WickNonzeroCore) where
  representation : ProperPoincareTransform →* (FockHilbert a ≃ₗᵢ[ℂ] FockHilbert a)
  same_original : representation=originalFockPoincareRepresentation a
  strongly_continuous : ∀ f,Continuous (fun g => representation g f)
  common_core : ∀ g (v : fockCoreDomain a),representation g v.val∈fockCoreDomain a
  transport_restriction : ∀ g probe,wickOriginalRoleOutput a s Ω u (.comparison g probe)=
    .probability (‖inner ℂ
      (finiteParticleCoreToFock a (originalWickUnitRepresentative a probe.val))
      (representation g (finiteParticleCoreToFock a (originalWickUnitRepresentative a u.val)))‖^2)

def wickRoleInertialWitness (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (u : WickNonzeroCore) : WickRoleInertialWitness a s Ω u where
  representation := originalFockPoincareRepresentation a
  same_original := rfl
  strongly_continuous := originalFockPoincareRepresentation_strongly_continuous a
  common_core := originalFockPoincareRepresentation_preserves_domain a
  transport_restriction := fun _ _ => rfl

def wickRoleQin (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) : Set (WickRoleQresp a s Ω) :=
  {q | ∃ u,wickRoleClassify a s Ω u=q ∧ Nonempty (WickRoleInertialWitness a s Ω u)}

def wickRoleQmass (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) : Set (WickRoleQresp a s Ω) :=
  wickRoleQin a s Ω ∩ wickRoleQsrcbase a s Ω

def wickRoleQmasshat (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) : Set (WickRoleQsrc a s Ω) :=
  wickRoleForget a s Ω ⁻¹' wickRoleQmass a s Ω

/-- The exact B02 intersection is occupied on this declared branch.
No numerical gravitational/inertial mass equality is a premise or conclusion. -/
theorem wick_role_original_source_in_mass_overlap (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (ray : Quotient wickCoreRaySetoid) :
    wickRolePiA a s Ω (wickRoleSx a s Ω ray)∈wickRoleQmasshat a s Ω := by
  constructor
  · exact ⟨ray.out,rfl,⟨wickRoleInertialWitness a s Ω ray.out⟩⟩
  · exact ⟨wickRolePiA a s Ω (wickRoleSx a s Ω ray),rfl⟩

theorem wick_role_calibrated_same_tensor_charge (a : Parameters)
    (Ω : Opens CoordinatePoint) (ray : Quotient wickCoreRaySetoid) (j : Fin 4) (τ : ℝ) :
    (∀ H : MetricSourceProbe Ω,(wickRoleSx a (wickPositiveCalibratedAmplitude a) Ω ray).attachment.functional H=
      (1/2 : ℝ)*∫ p,∑ i,∑ k,tensorEncode (H p) i k*
        wickOriginalNativeRealTensor a (wickPositiveCalibratedAmplitude a) (wickRayPresentationState a ray) p i k) ∧
    wickNativeTensorHypersurfaceCharge a (wickPositiveCalibratedAmplitude a)
      (wickRayPresentationState a ray) j τ=
      (inner ℂ (finiteParticleCoreToFock a (wickRayPresentationState a ray))
        (finiteParticleCoreToFock a (wickOriginalCoreFourMomentum a j (wickRayPresentationState a ray)))).re := by
  simpa only [wick_positive_calibrated_amplitude_coefficient,one_mul] using
    wick_native_ray_presentation_source_and_charge a (wickPositiveCalibratedAmplitude a) Ω ray j τ

end AASCKleinGordon
