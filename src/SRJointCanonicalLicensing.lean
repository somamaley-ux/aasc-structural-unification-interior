import SRJointSourceContinuations
import SRCommonFlatGeometry

/-! Canonical licensing of the declared actual joint coasting-use task.
The sound region is proved from positive source mass, interval order and
actual readout truth. This adapter does not yet assert all-frame naturality. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace AASCMetricConstruction
open AASC.KernelReference AASCMetricityOriginalAssembly AASCMetricityLicensingConstruction
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

abbrev JointContext := SRContextQuery JointQuestion JointOperation
abbrev JointContextValue : JointContext → Type :=
  srContextValue (Op:=JointOperation) (jointValue a s Ω)
abbrev JointProfile := (q : JointContext) → JointContextValue a s Ω q

structure JointSRUseMeaning where
  clockParameter : ℝ
  completeOriginalProfiles : JointOriginalSource a s Ω → JointProfile a s Ω
  sourceDerivedGeometry : QuadraticForm ℝ SREvent
  originalClockReadout : JointOriginalSource a s Ω → ℝ
  scalarContinuation : ℝ → JointOriginalSource a s Ω → JointOriginalSource a s Ω
  clockIntervalExtension : ℝ → JointOriginalSource a s Ω → JointOriginalSource a s Ω

def originalJointSRUseMeaning : JointSRUseMeaning a s Ω :=
  ⟨a.mass,jointCompleteObserve a s Ω,srOriginalOrderQuadratic,
    fun j => srNativeClockActualInterval a.mass j.clock,
    jointScalarContinue a s Ω,jointClockExtend a s Ω⟩

abbrev JointContinuation := ℝ ⊕ {δ : ℝ // 0 ≤ δ}

def jointContinue (t : JointContinuation) (j : JointOriginalSource a s Ω) : JointOriginalSource a s Ω :=
  match t with
  | .inl t => jointScalarContinue a s Ω t j
  | .inr δ => jointClockExtend a s Ω δ.val j

def jointContinuationWarrant (x : JointOriginalSource a s Ω) (t : JointContinuation)
    (y : JointOriginalSource a s Ω) : Prop :=
  y = jointContinue a s Ω t x ∧ srNativeClockUseValid a.mass y.clock ∧
    (∀ σ, srNativeCoastingMarkedRecord a.mass y.clock.record σ =
      srNativeCoastingMarkedRecord a.mass x.clock.record σ) ∧ y.metric = x.metric

def originalJointSRAnswer (ground : JointProfile a s Ω) :
    (q : Unit ⊕ JointContext) →
      ProfileValue (JointContextValue a s Ω) (JointSRUseMeaning a s Ω) q → Prop
  | .inl _ => fun meaning => meaning = originalJointSRUseMeaning a s Ω
  | .inr q => fun answer => answer = ground q

def originalJointSRTask :
    OriginalMetricTask (JointOriginalSource a s Ω) (JointOriginalSource a s Ω)
      (JointProfile a s Ω) (JointSRUseMeaning a s Ω) ℝ JointContinuation
      JointContext (JointContextValue a s Ω) (JointOriginalSource a s Ω)
      (JointSRUseMeaning a s Ω) (JointSRUseMeaning a s Ω) (JointProfile a s Ω) where
  act := id
  ground := jointCompleteObserve a s Ω
  descriptor := fun _ => originalJointSRUseMeaning a s Ω
  descriptorMeaning := id
  answers := jointCompleteObserve a s Ω
  qualification := fun ground x => jointCompleteObserve a s Ω x = ground ∧
    srNativeClockUseValid a.mass x.clock
  originalAnswer := originalJointSRAnswer a s Ω
  originalLocal := fun x => srNativeClockUseValid a.mass x.clock
  redescription := fun x y => ∃ h : ℝ, y = jointClockRebase a s Ω h x
  redEdge := fun x h y => y = jointClockRebase a s Ω h x
  contEdge := fun x t y => y = jointContinue a s Ω t x
  redOriginalWarrant := fun x h y => y = jointClockRebase a s Ω h x
  contOriginalWarrant := jointContinuationWarrant a s Ω
  context := fun _ => originalJointSRUseMeaning a s Ω
  boundaryWork := id

theorem original_joint_sr_answers_determinate :
    DependentConservation.Determinate (originalJointSRTask a s Ω).originalAnswer := by
  intro ground q x y hx hy
  cases q <;> exact hx.trans hy.symm

def jointSoundRegion : Set (JointOriginalSource a s Ω) :=
  {j | srNativeClockUseValid a.mass j.clock}

theorem actual_joint_sr_use_passes_local_tests (x : JointOriginalSource a s Ω)
    (valid : srNativeClockUseValid a.mass x.clock) :
    originalLocalTest (originalJointSRTask a s Ω) x := by
  refine ⟨⟨x,rfl,valid⟩,?_,valid,?_⟩
  · intro q
    cases q <;> rfl
  · intro y same
    obtain ⟨h,hh⟩ := same
    exact ⟨h,y,hh,rfl⟩

theorem original_joint_sr_region_postfixed :
    jointSoundRegion a s Ω ⊆ originalSafetyOperator (originalJointSRTask a s Ω) (jointSoundRegion a s Ω) := by
  intro x valid
  refine ⟨actual_joint_sr_use_passes_local_tests a s Ω x valid,?_⟩
  intro t y edge
  cases t with
  | inl h =>
    change y = jointClockRebase a s Ω h x at edge
    subst y
    exact ⟨⟨rfl,(joint_clock_rebase_complete_context_profile a s Ω h x)⟩,
      (joint_clock_rebase_preserves_validity a s Ω h x).mpr valid⟩
  | inr t =>
    change y = jointContinue a s Ω t x at edge
    subst y
    have nextValid : srNativeClockUseValid a.mass (jointContinue a s Ω t x).clock := by
      cases t with
      | inl t => exact valid
      | inr δ =>
        exact AASCMetricConstruction.SRIntegration.sr_native_clock_extension_valid
          a.mass δ.val x.clock valid δ.property
    have records : ∀ σ, srNativeCoastingMarkedRecord a.mass (jointContinue a s Ω t x).clock.record σ =
        srNativeCoastingMarkedRecord a.mass x.clock.record σ := by cases t <;> intro σ <;> rfl
    have metricSame : (jointContinue a s Ω t x).metric = x.metric := by cases t <;> rfl
    exact ⟨⟨rfl,nextValid,records,metricSame⟩,nextValid⟩

theorem actual_joint_sr_use_has_canonical_license (x : JointOriginalSource a s Ω)
    (valid : srNativeClockUseValid a.mass x.clock) :
    constructedLicensing (originalJointSRTask a s Ω) x (originalJointSRUseMeaning a s Ω) :=
  canonical_licensing_contains_every_original_sound_region _ (jointSoundRegion a s Ω)
    (original_joint_sr_region_postfixed a s Ω) x valid

theorem joint_sr_use_constructs_kernel_and_canonical_license :
    let D := originalJointSRTask a s Ω
    AASC.Instances.KernelPaper.Manuscript.DerivedKernelRoles
      (ObjecthoodNecessity.canonicalRegime (originalIncidence D)) ∧
    AASCAMetricMetricUse.AMetricLicensingDiscipline ∧ FiveLicensingConclusions D ∧
      (∀ x, srNativeClockUseValid a.mass x.clock →
        constructedLicensing D x (originalJointSRUseMeaning a s Ω)) := by
  let r := presentLicensedScalar a s Ω (scalarBaseObject a)
    (kgNRFamilyPreparation a (scalarBaseObject a).shape)
  obtain ⟨x,valid,_⟩ := joint_source_covers_every_old_preparation a s Ω r (srCommonFlatOperand Ω)
  have assembly := kernel_ametric_canonical_metric_licensing (originalJointSRTask a s Ω)
    (original_joint_sr_answers_determinate a s Ω)
    ⟨jointCompleteObserve a s Ω x,x,rfl,valid⟩
  exact ⟨assembly.1,assembly.2.2.1,assembly.2.2.2.2.2,actual_joint_sr_use_has_canonical_license a s Ω⟩

#print axioms original_joint_sr_region_postfixed
#print axioms joint_sr_use_constructs_kernel_and_canonical_license
end AASCKleinGordon.CanonicalLicensing.SRIntegration
