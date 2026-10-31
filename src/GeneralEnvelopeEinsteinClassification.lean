import CubicWitnessLorentzFrames
import NativeActionEinsteinResponse

/-! General-envelope coefficient discipline. The explicit divergence identity
is the S17 interpretation stated in CSP-C 2.5/Einstein 23.1. This module does
not claim to derive that interpretation from mere existential source matching. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open Filter
open scoped Topology

def GeneralNormalMetricResponseClosure (E : MetricFieldResponse) : Prop :=
  ∀ (g : MetricField), C3NormalizedMetricGerm g → coordinateDivergence g (E g) 0=0

def FullLorentzEnvelopeResponseActive (E : MetricFieldResponse) : Prop :=
  ¬ ∃ c : ℝ, ∀ (g : MetricField) (p : CoordinatePoint)
      (B : CoordinatePoint ≃L[ℝ] CoordinatePoint),
    MetricFieldSymmetric g → (∀ i j, ContDiffAt ℝ 2 (fun x => g x i j) p) →
      LorentzFrameAt g p B → E g p=c • g p

theorem full_envelope_activity_from_total_source_match (E : MetricFieldResponse)
    (g : MetricField) (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (hg : C2LorentzMetricAt g p) (hB : LorentzFrameAt g p B)
    (T : Tensor2) (matching : E g p=T) (total_active : ∀ c : ℝ, T≠c • g p) :
    FullLorentzEnvelopeResponseActive E := by
  rintro ⟨c,hc⟩
  exact total_active c (matching.symm.trans (hc g p B hg.1 hg.2.1 hB))

theorem regular_general_envelope_unique_einstein_response
    (E : MetricFieldResponse) (core : RegularLorentzResponseCore E)
    (general_closure : GeneralNormalMetricResponseClosure E)
    (active : FullLorentzEnvelopeResponseActive E) :
    ∃! ac : ℝ × ℝ, ac.1≠0 ∧ CoordinateEinsteinResponseForm E ac.1 ac.2 := by
  obtain ⟨coeff,hcoeff,unique⟩ := regular_lorentz_coordinate_response_normal_form E core
  rcases coeff with ⟨a,b,c⟩
  let g := cubicMetricField scalarGradientWitnessJet
  have germ : C3NormalizedMetricGerm g :=
    cubicMetricField_c3_normalized _ scalarGradientWitnessJet_metric_symmetry
  have hnear : E g =ᶠ[𝓝 0] a • coordinateRicci g+b • coordinateScalarMetric g+c • g := by
    filter_upwards [cubic_witness_lorentz_frames_near_zero] with p hp
    obtain ⟨B,hB⟩ := hp
    apply hcoeff g p B germ.1 _ hB
    intro i j
    exact (contDiff_const.add (cubicPolynomial_smooth (scalarGradientWitnessJet i j))).contDiffAt.of_le (by simp)
  have hdiv : coordinateDivergence g (a • coordinateRicci g+b • coordinateScalarMetric g+c • g) 0=0 := by
    rw [← coordinate_divergence_germ_congruence g _ _ hnear]
    exact general_closure g germ
  have hb := (c3_normal_geometric_coefficient_lock_iff g germ actual_scalar_gradient_witness_nonzero a b c).mp hdiv
  have hform : CoordinateEinsteinResponseForm E a c := by
    intro g p B hs hr hf
    rw [hcoeff g p B hs hr hf]
    exact MetricProjectionAudit.einstein_combination _ _ _ a b c hb
  have ha : a≠0 := by
    intro hz
    apply active
    refine ⟨c,?_⟩
    intro g p B hs hr hf
    rw [hform g p B hs hr hf,hz,zero_smul,zero_add]
  refine ⟨(a,c),⟨ha,hform⟩,?_⟩
  rintro ⟨a',c'⟩ ⟨_,other⟩
  have hother : ∀ (g : MetricField) (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
      (hs : MetricFieldSymmetric g) (hr : ∀ i j, ContDiffAt ℝ 2 (fun x => g x i j) p)
      (hf : LorentzFrameAt g p B),
      E g p=a' • coordinateRicci g p+(-a'/2) • coordinateScalarMetric g p+c' • g p := by
    intro g p B hs hr hf
    rw [other g p B hs hr hf]
    exact (MetricProjectionAudit.einstein_combination _ _ _ a' (-a'/2) c' rfl).symm
  have hu := unique (a',-a'/2,c') hother
  have hfirst : a'=a := congrArg Prod.fst hu
  have hlast : c'=c := congrArg (fun x : ℝ × ℝ × ℝ => x.2.2) hu
  exact Prod.ext hfirst hlast

#print axioms full_envelope_activity_from_total_source_match
#print axioms regular_general_envelope_unique_einstein_response
end
end AASCSemanticExhaustion
