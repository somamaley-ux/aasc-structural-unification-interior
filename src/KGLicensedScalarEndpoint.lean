import KGLicensedScalarReceiver
import KGS36FreeComparatorAssembly

/-! The existing free scalar endpoint, read through the actual licensed
description. Calibration remains an explicit premise for arbitrary comparators.
The license does not choose the declared continuum carrier or physical constants. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) (A : KGNRObject a)

theorem licensed_scalar_free_ssq1 (r : LicensedScalarReceiver a s Ω A) :
    SameScopeQuantumSpatial1 (licensedScalarMeaning a s Ω A r).parameters
      (licensedScalarHamiltonian a s Ω A r) (0 : KGSpatialSpace → ℝ) := by
  unfold licensedScalarHamiltonian
  rw [licensed_scalar_meaning_exact]
  exact kg_nr_free_ssq1 a

theorem licensed_scalar_reference_dispersion (r : LicensedScalarReceiver a s Ω A) :
    ∀ ξ, kgScalarPrincipalFourierSymbol
      (kgNRFreeComparator (licensedScalarMeaning a s Ω A r).parameters).data ξ =
        ((licensedScalarMeaning a s Ω A r).referenceDispersion ξ : ℂ) := by
  rw [licensed_scalar_meaning_exact]
  exact kg_nr_free_comparator_inertial_dispersion a

theorem licensed_scalar_zero_potential_full_domain (r : LicensedScalarReceiver a s Ω A) :
    (∀ f : KGNRSpatialHilbert,
      f ∈ (kgNRPotentialOperator (0 : KGSpatialSpace → ℝ)).domain) ∧
    kgNRPrincipalCoefficient (licensedScalarMeaning a s Ω A r).parameters =
      -(a.hbar ^ 2 / (2 * a.mass)) ∧
    kgNRPrincipalCoefficient (licensedScalarMeaning a s Ω A r).parameters < 0 := by
  rw [licensed_scalar_meaning_exact]
  exact ⟨kg_nr_zero_potential_domain, rfl, kg_nr_principal_coefficient_negative a⟩

theorem licensed_scalar_ssq1_comparator (r : LicensedScalarReceiver a s Ω A)
    {H : LinearPMap ℂ KGNRSpatialHilbert KGNRSpatialHilbert}
    (W : KGScalarSSQ1Witness a H (0 : KGSpatialSpace → ℝ))
    (dispersion : KGFreeInertialDispersion a (kgScalarFreeComparatorOfSSQ1 a W)) :
    H = licensedScalarHamiltonian a s Ω A r :=
  licensed_scalar_calibrated_comparator a s Ω A r (kgScalarFreeComparatorOfSSQ1 a W)
    (dispersion kgScalarCalibrationFrequency)

end AASCKleinGordon.CanonicalLicensing
