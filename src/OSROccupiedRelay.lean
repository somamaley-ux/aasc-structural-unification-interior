import OSRRestNetwork
import SRNativeFiniteReflectionProtocol

/-! A positive-delay relay is an extended optical path. Intermediate Y
crossings are labels on the same main ray, not new scattering vertices. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR
attribute [local instance] Classical.propDecidable

structure RelayData where
  X : SRSpace
  direction : SRSpace
  length : ℝ
  delay : ℝ
  emit : ℝ
  energy : ℝ

def relayLength (R : RelayData) : ℝ := R.length+R.delay/2
def relayY (R : RelayData) : SRSpace := R.X+R.length • R.direction
def relayZ (R : RelayData) : SRSpace := R.X+relayLength R • R.direction
def relayDeparture (R : RelayData) : SREvent := (R.emit,R.X)
def relayArrival (R : RelayData) : SREvent := (R.emit+R.length,relayY R)
def relayTurn (R : RelayData) : SREvent := (R.emit+relayLength R,relayZ R)
def relayRelease (R : RelayData) : SREvent := (R.emit+R.length+R.delay,relayY R)
def relayReturn (R : RelayData) : SREvent := (R.emit+2*R.length+R.delay,R.X)

def relayMainPosition (R : RelayData) (t : ℝ) : SRSpace :=
  if t ≤ (relayTurn R).1 then R.X+(t-R.emit) • R.direction
  else R.X+((relayReturn R).1-t) • R.direction

def relayMainMomentum (R : RelayData) (t : ℝ) : SREvent :=
  srNativePositiveRayMomentum R.energy (if t ≤ (relayTurn R).1 then R.direction else -R.direction)

def relayCompensatorPosition (R : RelayData) (t : ℝ) : SRSpace :=
  if t ≤ (relayTurn R).1 then relayZ R+((relayTurn R).1-t) • R.direction
  else relayZ R+(t-(relayTurn R).1) • R.direction

theorem relay_main_crossing_records (R : RelayData) (length : 0 < R.length) (delay : 0 ≤ R.delay) :
    relayMainPosition R (relayDeparture R).1=R.X ∧
    relayMainPosition R (relayArrival R).1=relayY R ∧
    relayMainPosition R (relayTurn R).1=relayZ R ∧
    relayMainPosition R (relayRelease R).1=relayY R ∧
    relayMainPosition R (relayReturn R).1=R.X := by
  have dep : (relayDeparture R).1 ≤ (relayTurn R).1 := by dsimp [relayDeparture,relayTurn,relayLength];linarith
  have arr : (relayArrival R).1 ≤ (relayTurn R).1 := by dsimp [relayArrival,relayTurn,relayLength];linarith
  have ret : ¬ (relayReturn R).1 ≤ (relayTurn R).1 := by dsimp [relayReturn,relayTurn,relayLength];linarith
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [relayMainPosition,if_pos dep]
    simp [relayDeparture]
  · rw [relayMainPosition,if_pos arr]
    simp [relayArrival,relayY]
  · simp [relayMainPosition,relayTurn,relayZ]
  · by_cases zero : R.delay=0
    · have eq : relayRelease R=relayTurn R := by
        apply Prod.ext
        · simp [relayRelease,relayTurn,relayLength,zero]
        · simp [relayRelease,relayTurn,relayZ,relayY,relayLength,zero]
      rw [eq]
      simp [relayMainPosition,relayTurn,relayZ,relayLength,zero,relayY]
    · have leave : ¬ (relayRelease R).1 ≤ (relayTurn R).1 := by
        dsimp [relayRelease,relayTurn,relayLength];have pos : 0 < R.delay := lt_of_le_of_ne delay (Ne.symm zero);linarith
      rw [relayMainPosition,if_neg leave]
      dsimp [relayRelease,relayReturn,relayY]
      congr 2
      ring
  · rw [relayMainPosition,if_neg ret]
    simp [relayReturn]

theorem relay_compensator_shared_vertex (R : RelayData) :
    relayCompensatorPosition R (relayTurn R).1=relayZ R := by
  simp [relayCompensatorPosition]

theorem relay_full_legs_are_actual_original_rays (R : RelayData) (length : 0 < R.length)
    (delay : 0 ≤ R.delay) (unit : ‖R.direction‖=1) :
    relayTurn R-relayDeparture R ∈ srOriginalFutureRayIncrements ∧
    relayReturn R-relayTurn R ∈ srOriginalFutureRayIncrements := by
  have positive : 0 < relayLength R := by dsimp [relayLength];linarith
  have forward : relayTurn R-relayDeparture R=(relayLength R,relayLength R • R.direction) := by
    apply Prod.ext <;> simp [relayTurn,relayDeparture,relayZ]
  have backward : relayReturn R-relayTurn R=(relayLength R,relayLength R • (-R.direction)) := by
    apply Prod.ext
    · dsimp [relayReturn,relayTurn,relayLength];ring
    · simp [relayReturn,relayTurn,relayZ,smul_neg]
  rw [forward,backward]
  exact ⟨(sr_native_positive_energy_ray_is_original_future_null _ positive _ unit).1,
    (sr_native_positive_energy_ray_is_original_future_null _ positive _ (by simpa using unit)).1⟩

theorem relay_positive_energy_and_balanced_vertex (R : RelayData) (energy : 0 < R.energy)
    (unit : ‖R.direction‖=1) (mu : ℝ) :
    srNativePositiveRayMomentum R.energy R.direction ∈ srOriginalFutureRayIncrements ∧
    srNativePositiveRayMomentum R.energy (-R.direction) ∈ srOriginalFutureRayIncrements ∧
    ((mu,(0:SRSpace))+srNativePositiveRayMomentum R.energy R.direction+
      srNativePositiveRayMomentum R.energy (-R.direction))=
    ((mu,(0:SRSpace))+srNativePositiveRayMomentum R.energy (-R.direction)+
      srNativePositiveRayMomentum R.energy R.direction) := by
  exact ⟨(sr_native_positive_energy_ray_is_original_future_null _ energy _ unit).1,
    (sr_native_positive_energy_ray_is_original_future_null _ energy _ (by simpa using unit)).1,
    sr_native_balanced_reflection_preserves_total_momentum_and_endpoint mu R.energy R.direction R.direction⟩

def relayAtSites {n : ℕ} (S : SiteData n) (i j : Fin (n+1)) (emit delay energy : ℝ) : RelayData :=
  ⟨S.position i,(‖S.position j-S.position i‖)⁻¹ • (S.position j-S.position i),
    ‖S.position j-S.position i‖,delay,emit,energy⟩

theorem relay_at_distinct_sites_geometry {n : ℕ} (S : SiteData n) (i j : Fin (n+1))
    (distinct : S.position j ≠ S.position i) (emit delay energy : ℝ) :
    0 < (relayAtSites S i j emit delay energy).length ∧
    ‖(relayAtSites S i j emit delay energy).direction‖=1 ∧
    relayY (relayAtSites S i j emit delay energy)=S.position j := by
  have positive : 0 < ‖S.position j-S.position i‖ := norm_pos_iff.mpr (sub_ne_zero.mpr distinct)
  refine ⟨positive,?_,?_⟩
  · change ‖(‖S.position j-S.position i‖)⁻¹ • (S.position j-S.position i)‖=1
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr positive),inv_mul_cancel₀ positive.ne']
  · change S.position i+‖S.position j-S.position i‖ •
      ((‖S.position j-S.position i‖)⁻¹ • (S.position j-S.position i))=S.position j
    rw [smul_smul,mul_inv_cancel₀ positive.ne',one_smul,add_sub_cancel]

def siteReading (mu0 : ℝ) {n : ℕ} (S : SiteData n) (i : Fin (n+1)) (t : ℝ) : ℝ :=
  (srNativeCoastingMarkedRecord mu0 (siteRecord mu0 S i) t).2.reading

theorem occupied_radar_readings (mu0 : ℝ) {n : ℕ} (S : SiteData n) (i j : Fin (n+1))
    (positive_i : 0 < mu0+S.internalEnergy i) (positive_j : 0 < mu0+S.internalEnergy j)
    (emit delay energy : ℝ) :
    let R := relayAtSites S i j emit delay energy
    siteReading mu0 S j (relayArrival R).1-
      (siteReading mu0 S i (relayDeparture R).1+siteReading mu0 S i (relayReturn R).1-delay)/2=S.phase j-S.phase i ∧
    siteReading mu0 S j (relayRelease R).1-siteReading mu0 S j (relayArrival R).1=delay ∧
    (siteReading mu0 S i (relayReturn R).1-siteReading mu0 S i (relayDeparture R).1-delay)/2=R.length := by
  dsimp only
  simp only [siteReading,site_actual_reading mu0 S i positive_i,site_actual_reading mu0 S j positive_j]
  dsimp [relayAtSites,relayArrival,relayRelease,relayReturn,relayDeparture]
  constructor
  · ring
  · constructor <;> ring_nf

theorem recorded_delay_arrival_departure (tm tp d arrival departure : ℝ)
    (midpoint : arrival=(tm+tp-d)/2) (delay : departure-arrival=d) :
    arrival=(tm+tp-d)/2 ∧ departure=(tm+tp+d)/2 := by
  constructor
  · exact midpoint
  · rw [midpoint] at delay
    linarith

def phasePath {ι : Type} (phase : ι → ℝ) : List ι → ℝ
  | [] => 0
  | [_] => 0
  | i::j::tail => (phase j-phase i)+phasePath phase (j::tail)

def pathEnd {ι : Type} : ι → List ι → ι
  | i,[] => i
  | _,j::tail => pathEnd j tail

theorem phase_path_telescope {ι : Type} (phase : ι → ℝ) (i : ι) (tail : List ι) :
    phasePath phase (i::tail)=phase (pathEnd i tail)-phase i := by
  induction tail generalizing i with
  | nil => simp [phasePath,pathEnd]
  | cons j tail ih =>
    rw [phasePath,ih]
    dsimp [pathEnd]
    ring

theorem phase_path_loop_zero {ι : Type} (phase : ι → ℝ) (i : ι) (tail : List ι)
    (closed : pathEnd i tail=i) : phasePath phase (i::tail)=0 := by
  rw [phase_path_telescope,closed,sub_self]

end AASCKleinGordon.OperationalSR
