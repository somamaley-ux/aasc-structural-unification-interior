import RCUniformMomentum
import KGNRSourceRecordTransport
import KGNRFreeReceivingAssembly

/-! Actual preparation/normalization and physical Fourier recovery maps.
The finite-c cutoff lives in full L2, while limiting source records retain
their separately proved original invariant-core preparation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open MeasureTheory Filter
open scoped Topology
namespace AASCKleinGordon.RecoveryComparison

def covariantRecoveryPreparation (a : Parameters) (c : ℝ) (hc : 0 < c)
    (f : KGNRMomentumHilbert) : WickCovariantHilbert (kgNRParameters a c hc) :=
  (kgCovariantMomentumUnitary (kgNRParameters a c hc)).symm f

def isolatedRecoveryPreparation (a : Parameters) (c : ℝ) (hc : 0 < c)
    (f : KGNRMomentumHilbert) : wickIsolatedOneParticleSpace (kgNRParameters a c hc) :=
  (kgIsolatedMomentumUnitary (kgNRParameters a c hc)).symm f

theorem actual_covariant_preparation_evolution_square (a : Parameters) (c : ℝ) (hc : 0 < c)
    (t : ℝ) (f : KGNRMomentumHilbert) :
    kgCovariantMomentumUnitary (kgNRParameters a c hc)
      (kgNRActualCovariantRestFlow a c hc t (covariantRecoveryPreparation a c hc f)) =
      kgNRMomentumFlow a c t f := by
  rw [kg_covariant_original_rest_flat_intertwining]
  simp only [covariantRecoveryPreparation,LinearIsometryEquiv.apply_symm_apply]

theorem actual_isolated_preparation_evolution_square (a : Parameters) (c : ℝ) (hc : 0 < c)
    (t : ℝ) (f : KGNRMomentumHilbert) :
    kgIsolatedMomentumUnitary (kgNRParameters a c hc)
      (kgNRActualIsolatedRestFlow a c hc t (isolatedRecoveryPreparation a c hc f)) =
      kgNRMomentumFlow a c t f := by
  rw [kg_isolated_original_rest_flat_intertwining]
  simp only [isolatedRecoveryPreparation,LinearIsometryEquiv.apply_symm_apply]

def spatialCutoff (a : Parameters) (P : ℝ) : KGNRSpatialHilbert →L[ℂ] KGNRSpatialHilbert :=
  (kgPhysicalSpatialUnitary a).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((momentumCutoff P).comp (kgPhysicalSpatialUnitary a).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem physical_fourier_comparison_norm (a : Parameters) (c t : ℝ) (f : KGNRSpatialHilbert) :
    ‖kgOriginalRestSpatialFlow a c t f-kgNRSpatialFreeFlow a t f‖ =
      ‖kgTransportedIsolatedRestFlow a c t ((kgPhysicalSpatialUnitary a).symm f)-
        kgNRFreeMomentumFlow a t ((kgPhysicalSpatialUnitary a).symm f)‖ := by
  change ‖kgPhysicalSpatialUnitary a _-kgPhysicalSpatialUnitary a _‖ = _
  rw [←map_sub,LinearIsometryEquiv.norm_map]
  rfl

theorem spatial_cutoff_evolution_bound (a : Parameters) (c : ℝ) (hc : 0 < c)
    (t P : ℝ) (f : KGNRSpatialHilbert) :
    ‖kgOriginalRestSpatialFlow a c t (spatialCutoff a P f)-
      kgNRSpatialFreeFlow a t (spatialCutoff a P f)‖ ≤ min 2 (cutoffError a c t P)*‖f‖ := by
  rw [physical_fourier_comparison_norm]
  change ‖kgTransportedIsolatedRestFlow a c t ((kgPhysicalSpatialUnitary a).symm
      (kgPhysicalSpatialUnitary a (momentumCutoff P ((kgPhysicalSpatialUnitary a).symm f))))-
    kgNRFreeMomentumFlow a t ((kgPhysicalSpatialUnitary a).symm
      (kgPhysicalSpatialUnitary a (momentumCutoff P ((kgPhysicalSpatialUnitary a).symm f))))‖ ≤ _
  simp only [LinearIsometryEquiv.symm_apply_apply]
  simpa only [LinearIsometryEquiv.norm_map] using
    original_isolated_cutoff_bound a c hc t P ((kgPhysicalSpatialUnitary a).symm f)

theorem spatial_compact_time_strong (a : Parameters) (f : KGNRSpatialHilbert)
    (T : ℝ) (hT : 0 ≤ T) (epsilon : ℝ) (positive : 0 < epsilon) :
    ∀ᶠ c : ℝ in atTop, ∀ t : ℝ, |t| ≤ T →
      ‖kgOriginalRestSpatialFlow a c t f-kgNRSpatialFreeFlow a t f‖ < epsilon := by
  filter_upwards [original_isolated_compact_time_strong a ((kgPhysicalSpatialUnitary a).symm f)
    T hT epsilon positive] with c hc
  intro t ht
  rw [physical_fourier_comparison_norm]
  exact hc t ht

theorem original_core_compact_time_strong (a : Parameters) (x : kgOriginalSpatialCore a)
    (T : ℝ) (hT : 0 ≤ T) (epsilon : ℝ) (positive : 0 < epsilon) :
    ∀ᶠ c : ℝ in atTop, ∀ t : ℝ, |t| ≤ T →
      ‖kgOriginalRestSpatialFlow a c t x.val-(kgNRSpatialCoreFlow a t x).val‖ < epsilon := by
  filter_upwards [spatial_compact_time_strong a x.val T hT epsilon positive] with c hc
  intro t ht
  rw [kg_nr_spatial_core_flow_full_value a t x]
  exact hc t ht

end AASCKleinGordon.RecoveryComparison
