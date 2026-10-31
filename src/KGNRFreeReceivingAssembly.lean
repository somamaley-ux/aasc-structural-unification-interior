import KGNRReceivingCertificate
import KGNRFreeExactGenerator

/-! A concrete free autonomous three-dimensional receiving instance.
The declared continuum carrier and action/inertial calibration are inherited
from the actual KG rest-subtracted/Fourier construction. No classification
of all SSQ1 candidates, metric receiver, or new public release is asserted. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace AASCSemanticExhaustion
open scoped SchwartzMap

theorem kg_nr_free_receiving_ssq1
    (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    KGNRReceivingQS a s Ω ∧
    SameScopeQuantumSpatial1 a
      (kgNRSpatialKinetic a)
      (0 : KGSpatialSpace → ℝ) :=
  ⟨kg_nr_receiving_qs_constructed a s Ω,kg_nr_free_ssq1 a⟩

theorem kg_nr_free_receiving_exact_graph (a : Parameters) :
    GlobalCharge.ExactGenerator (Translation.coefficient a.hbar)
      (kgNRSpatialFreeFlow a) (kgNRSpatialKinetic a) ∧
    (∀ f g : KGNRSpatialHilbert,(f,g) ∈ (kgNRSpatialKinetic a).graph ↔
      ∀ test : 𝓢(KGSpatialSpace,ℂ),
        (g : KGSpatialDistribution) test =
          (f : KGSpatialDistribution) (kgNRSpatialTestResponse a test)) ∧
    (∀ f : KGNRSpatialHilbert,f ∈ (kgNRPotentialOperator (0 : KGSpatialSpace → ℝ)).domain) ∧
    (kgNRPrincipalCoefficient a = -(a.hbar^2/(2*a.mass)) ∧ kgNRPrincipalCoefficient a < 0) :=
  ⟨kg_nr_spatial_exact_generator a,kg_nr_spatial_kinetic_test_graph a,
    kg_nr_zero_potential_domain, rfl,kg_nr_principal_coefficient_negative a⟩

end AASCKleinGordon
