import KGCommonLicensedPreparation

/-! The scalar flow's actual original preparation in the common-source map.
This is a preparation correspondence, not an EH history-continuation law. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

theorem licensed_scalar_evolved_original_preparation (t : ℝ)
    (r : LicensedScalarReceiver a s Ω (scalarBaseObject a)) :
    licensedScalarOriginalPure a s Ω (scalarBaseObject a)
      (licensedScalarContinue a s Ω (scalarBaseObject a) t r) =
      kgNRSpatialOriginalPreparation a t (licensedScalarPure a s Ω (scalarBaseObject a) r) := by
  unfold licensedScalarOriginalPure
  rw [licensed_scalar_meaning_exact]
  exact kg_nr_spatial_core_original_preparation_square a t _

theorem common_evolved_original_preparation_square (κ Λ : ℝ) (coupling : κ ≠ 0)
    (t : ℝ) (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}) :
    kgPreparedQuantum s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
      (restrictedEHPrepared a s Ω (licensedEHResponse a s Ω
        (scalarToLicensedMetric a s Ω κ Λ coupling
          (licensedScalarContinue a s Ω (scalarBaseObject a) t r) H))) =
      rayMap _ (kgNRSpatialOriginalPreparation a t
        (licensedScalarPure a s Ω (scalarBaseObject a) r)) := by
  rw [common_original_preparation_square, licensed_scalar_evolved_original_preparation]
  rfl

theorem common_preparation_covers_declared_core (κ Λ : ℝ) (coupling : κ ≠ 0)
    (x : PureVector (kgOriginalSpatialCore a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}) :
    ∃ r : LicensedScalarReceiver a s Ω (scalarBaseObject a),
      licensedScalarPure a s Ω (scalarBaseObject a) r = x ∧
      kgPreparedQuantum s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
        (restrictedEHPrepared a s Ω (licensedEHResponse a s Ω
          (scalarToLicensedMetric a s Ω κ Λ coupling r H))) =
        rayMap _ (kgPureIsometryMap (kgSpatialCoreOriginalEmbedding a) x) := by
  refine ⟨presentLicensedScalar a s Ω (scalarBaseObject a) x, rfl, ?_⟩
  rw [common_original_preparation_square]
  unfold licensedScalarOriginalPure
  rw [licensed_scalar_meaning_exact]
  rfl

end AASCKleinGordon.CanonicalLicensing
