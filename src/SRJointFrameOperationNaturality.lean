import SRPassiveClockOperationTransport
import SRLicensedJointEvolution

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open KGQuantum W9 TopologicalSpace
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

def jointPassiveFrame (A : SRMatrixFrame) (b : SREvent) (j : JointOriginalSource a s Ω) :
    JointOriginalSource a s Ω := {j with clock := srPassiveClockUse a.mass A b j.clock}

def transportJointOperation (α : ℝ) : JointOperation → JointOperation
  | .clockRebase h => .clockRebase (α*h)
  | .scalarContinue t => .scalarContinue t
  | .clockExtend δ => .clockExtend (α*δ)
  | .certifyClockInterval => .certifyClockInterval

theorem joint_source_ext (j k : JointOriginalSource a s Ω)
    (clock : j.clock=k.clock) (scalar : j.scalar=k.scalar) (metric : j.metric=k.metric) : j=k := by
  cases j
  cases k
  simp_all

theorem joint_passive_registered_operation_square (source : SRCalibratedFrameSource a.mass)
    (A : SRMatrixFrame) (ha : A ∈ source.comparisons) (b : SREvent)
    (op : JointOperation) (j : JointOriginalSource a s Ω)
    (positive : 0 < srNativeClockMass a.mass j.clock.record.2.2) :
    jointOperation a s Ω (transportJointOperation
      (srPassiveClockSlope a.mass A j.clock.record.2.2) op) (jointPassiveFrame a s Ω A b j) =
        (jointOperation a s Ω op j).map (jointPassiveFrame a s Ω A b) := by
  cases op with
  | clockRebase h =>
    simp only [transportJointOperation,jointOperation,Option.map_some]
    congr 1
    apply joint_source_ext a s Ω
    · exact (sr_passive_clock_use_rebase a.mass a.mass_pos source A ha b j.clock h positive).symm
    · rfl
    · rfl
  | scalarContinue t => rfl
  | clockExtend δ =>
    have slope := sr_passive_clock_slope_positive a.mass source A ha j.clock.record.2.2 positive
    simp only [transportJointOperation,jointOperation,mul_nonneg_iff_of_pos_left slope]
    split
    · simp only [Option.map_some]
      congr 1
      apply joint_source_ext a s Ω
      · exact (sr_passive_clock_use_extension a.mass a.mass_pos source A ha b j.clock δ positive).symm
      · rfl
      · rfl
    · rfl
  | certifyClockInterval =>
    simp only [transportJointOperation,jointOperation]
    change (if srNativeClockUseValid a.mass (srPassiveClockUse a.mass A b j.clock) then
      some (jointPassiveFrame a s Ω A b j) else none) = _
    rw [sr_passive_clock_use_has_exact_original_eligibility a.mass a.mass_pos source A ha b j.clock]
    split <;> rfl

theorem joint_operation_preserves_clock_mass_and_slope (A : SRMatrixFrame)
    (op : JointOperation) (j k : JointOriginalSource a s Ω)
    (success : jointOperation a s Ω op j = some k) :
    srNativeClockMass a.mass k.clock.record.2.2 = srNativeClockMass a.mass j.clock.record.2.2 ∧
      srPassiveClockSlope a.mass A k.clock.record.2.2 = srPassiveClockSlope a.mass A j.clock.record.2.2 := by
  cases op with
  | clockRebase h =>
    simp only [jointOperation,Option.some.injEq] at success
    subst k
    exact ⟨rfl,rfl⟩
  | scalarContinue t =>
    simp only [jointOperation,Option.some.injEq] at success
    subst k
    exact ⟨rfl,rfl⟩
  | clockExtend δ =>
    simp only [jointOperation] at success
    split at success
    · have same := Option.some.inj success
      subst k
      exact ⟨rfl,rfl⟩
    · contradiction
  | certifyClockInterval =>
    simp only [jointOperation] at success
    split at success
    · have same := Option.some.inj success
      subst k
      exact ⟨rfl,rfl⟩
    · contradiction

theorem joint_passive_every_finite_first_failure_square (source : SRCalibratedFrameSource a.mass)
    (A : SRMatrixFrame) (ha : A ∈ source.comparisons) (b : SREvent)
    (ops : List JointOperation) (j : JointOriginalSource a s Ω)
    (positive : 0 < srNativeClockMass a.mass j.clock.record.2.2) :
    jointFirstFailure a s Ω
      (ops.map (transportJointOperation (srPassiveClockSlope a.mass A j.clock.record.2.2)))
      (jointPassiveFrame a s Ω A b j) = jointFirstFailure a s Ω ops j := by
  induction ops generalizing j with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.map_cons,jointFirstFailure,
      joint_passive_registered_operation_square a s Ω source A ha b op j positive]
    cases he : jointOperation a s Ω op j with
    | none => rfl
    | some k =>
      have invariants := joint_operation_preserves_clock_mass_and_slope a s Ω A op j k he
      simp only [Option.map_some]
      rw [← invariants.2]
      exact congrArg (Option.map Nat.succ) (ih k (invariants.1.symm ▸ positive))

theorem licensed_sr_clock_extension_frame_naturality (source : SRCalibratedFrameSource a.mass)
    (A : SRMatrixFrame) (ha : A ∈ source.comparisons) (b : SREvent)
    (δ : {δ : ℝ // 0 ≤ δ}) (r : LicensedJointSRReceiver a s Ω) :
    licensedSRPassiveFrame a s Ω source A ha b (licensedJointSRContinue a s Ω (.inr δ) r) =
      licensedJointSRContinue a s Ω
        (.inr ⟨srPassiveClockSlope a.mass A (licensedJointSRSource a s Ω r).clock.record.2.2*δ.val,
          mul_nonneg (sr_passive_clock_slope_positive a.mass source A ha _
            (licensed_joint_sr_has_actual_valid_source a s Ω r).1).le δ.property⟩)
        (licensedSRPassiveFrame a s Ω source A ha b r) := by
  apply licensed_joint_source_injective a s Ω
  apply joint_source_ext a s Ω
  · exact sr_passive_clock_use_extension a.mass a.mass_pos source A ha b _ δ.val
      (licensed_joint_sr_has_actual_valid_source a s Ω r).1
  · rfl
  · rfl

#print axioms joint_passive_registered_operation_square
#print axioms joint_passive_every_finite_first_failure_square
#print axioms licensed_sr_clock_extension_frame_naturality
end AASCKleinGordon.CanonicalLicensing.SRIntegration
