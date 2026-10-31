import OSRClockFrameTransport
import SRPassiveClockOperationTransport

/-! Primitive finite site data produce actual continuous coasting records.
Site identities are additional labels; they are not compressed into Fin 2. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR

def restUnit : SREvent := (1,0)

theorem restUnit_future : IsFutureUnit restUnit := by
  refine ⟨by norm_num [restUnit],?_⟩
  rw [sr_original_order_quadratic_computed]
  norm_num [restUnit]

structure SiteData (n : ℕ) where
  position : Fin (n+1) → SRSpace
  internalEnergy : Fin (n+1) → ℝ
  phase : Fin (n+1) → ℝ

def siteRecord (mu0 : ℝ) {n : ℕ} (S : SiteData n) (i : Fin (n+1)) :
    Fin 2 × (ℝ × SRNativeClockState SRSpace) :=
  (0,0,directionalClock mu0 (S.internalEnergy i) restUnit (S.position i) (S.phase i))

def siteUse (mu0 : ℝ) {n : ℕ} (S : SiteData n) (i : Fin (n+1)) (lo hi : ℝ) : SRNativeClockUse SRSpace :=
  ⟨siteRecord mu0 S i,lo,hi,hi-lo⟩

theorem site_actual_event (mu0 : ℝ) {n : ℕ} (S : SiteData n) (i : Fin (n+1))
    (positive : 0 < mu0+S.internalEnergy i) (t : ℝ) :
    srMarkedClockEvent mu0 (siteRecord mu0 S i) t=(t,S.position i) := by
  have actual := directional_clock_actual_event mu0 (S.internalEnergy i) positive restUnit restUnit_future
    (S.position i) (S.phase i) 0 t
  simpa [siteRecord,srMarkedClockEvent,srNativeCoastingMarkedRecord,restUnit] using actual

theorem site_actual_reading (mu0 : ℝ) {n : ℕ} (S : SiteData n) (i : Fin (n+1))
    (positive : 0 < mu0+S.internalEnergy i) (t : ℝ) :
    (srNativeCoastingMarkedRecord mu0 (siteRecord mu0 S i) t).2.reading=S.phase i+t := by
  have actual := directional_clock_actual_reading mu0 (S.internalEnergy i) positive restUnit restUnit_future
    (S.position i) (S.phase i) t
  simpa [siteRecord,srNativeCoastingMarkedRecord,restUnit] using actual

theorem site_use_actually_valid (mu0 : ℝ) {n : ℕ} (S : SiteData n) (i : Fin (n+1))
    (positive : 0 < mu0+S.internalEnergy i) (lo hi : ℝ) (ordered : lo ≤ hi) :
    srNativeClockUseValid mu0 (siteUse mu0 S i lo hi) := by
  refine ⟨positive,ordered,?_⟩
  change hi-lo=(srNativeCoastingMarkedRecord mu0 (siteRecord mu0 S i) hi).2.reading-
    (srNativeCoastingMarkedRecord mu0 (siteRecord mu0 S i) lo).2.reading
  rw [site_actual_reading mu0 S i positive,site_actual_reading mu0 S i positive]
  ring

def framedSiteUse (mu0 : ℝ) {n : ℕ} (S : SiteData n) (i : Fin (n+1))
    (lo hi : ℝ) (A : SRMatrixFrame) (b : SREvent) (epoch : ℝ) : SRNativeClockUse SRSpace :=
  srNativeClockUseRedescription mu0 epoch (srPassiveClockUse mu0 A b (siteUse mu0 S i lo hi))

theorem framed_site_use_actually_valid (mu0 : ℝ) (base : 0 < mu0) {n : ℕ}
    (S : SiteData n) (i : Fin (n+1)) (positive : 0 < mu0+S.internalEnergy i)
    (lo hi : ℝ) (ordered : lo ≤ hi) (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons)
    (b : SREvent) (epoch : ℝ) : srNativeClockUseValid mu0 (framedSiteUse mu0 S i lo hi A b epoch) := by
  apply (sr_native_clock_original_use_domain_and_answer_preserved mu0 epoch _).mpr
  exact (sr_passive_clock_use_has_exact_original_eligibility mu0 base (srNativeOccupiedFrameSource mu0 base)
    A admitted b _).mpr (site_use_actually_valid mu0 S i positive lo hi ordered)

theorem site_phases_are_actual_offsets (mu0 : ℝ) {n : ℕ} (S : SiteData n) (i j : Fin (n+1))
    (positive_i : 0 < mu0+S.internalEnergy i) (positive_j : 0 < mu0+S.internalEnergy j) (t : ℝ) :
    (srNativeCoastingMarkedRecord mu0 (siteRecord mu0 S j) t).2.reading-
      (srNativeCoastingMarkedRecord mu0 (siteRecord mu0 S i) t).2.reading=S.phase j-S.phase i := by
  rw [site_actual_reading mu0 S j positive_j,site_actual_reading mu0 S i positive_i]
  ring

end AASCKleinGordon.OperationalSR
