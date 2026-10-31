import KGScalarComparatorFourier
import KGNRFreeReceivingAssembly

/-! A bounded source-faithful free S36 comparator endpoint. Unlike fixed-flow
uniqueness, this compares independently supplied operators via declared
finite-jet/domain data and admitted inertial dispersion. No same-U or desired
operator identity is an input. General paper-predicate equivalence is separate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace AASCSemanticExhaustion

theorem kg_source_free_s36_comparator_endpoint
    (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    KGNRReceivingQS a s Ω ∧
    KGFreeInertialDispersion a (kgNRFreeComparator a) ∧
    (∀ (H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert)
      (C : KGScalarFreeComparator H),
      KGFreeAnchoredDispersionAt a C → H = kgNRSpatialKinetic a) ∧
    (∀ (H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert)
      (W : KGScalarSSQ1Witness a H (0 : KGSpatialSpace → ℝ)),
      KGFreeInertialDispersion a (kgScalarFreeComparatorOfSSQ1 a W) →
        H = kgNRSpatialKinetic a) := by
  refine ⟨kg_nr_receiving_qs_constructed a s Ω,
    kg_nr_free_comparator_inertial_dispersion a,?_,?_⟩
  · intro H C calibration
    exact kg_free_calibrated_comparator_eq a C calibration
  · intro H W dispersion
    exact kg_free_calibrated_comparator_eq a (kgScalarFreeComparatorOfSSQ1 a W)
      (dispersion kgScalarCalibrationFrequency)

theorem kg_calibrated_free_comparator_exact_generator
    (a : Parameters) {H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert}
    (C : KGScalarFreeComparator H) (calibration : KGFreeAnchoredDispersionAt a C) :
    GlobalCharge.ExactGenerator (Translation.coefficient a.hbar) (kgNRSpatialFreeFlow a) H := by
  rw [kg_free_calibrated_comparator_eq a C calibration]
  exact kg_nr_spatial_exact_generator a

end AASCKleinGordon
