import NativeActionClassicalSource
import CoordinateMetricResponseNormalForm
import ScalarSourceMetricCompatibility

/-! Conditional receiving theorem at the native action-presentable source
interface. Curvature exhaustion, distributional/classical source conservation,
coefficient locking and activity are derived in one chain. The candidate field
matching is E=κT, not a preselected Einstein equation. The receiving Lorentzian
projection, complete native action receipts and an admitted nonzero-gradient,
nonbaseline source witness remain explicit. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open Filter TopologicalSpace MeasureTheory
open scoped Topology

def CoordinateEinsteinResponseForm (E : MetricFieldResponse) (a c : ℝ) : Prop :=
  ∀ (g : MetricField) (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint),
    MetricFieldSymmetric g → (∀ i j, ContDiffAt ℝ 2 (fun x => g x i j) p) → LorentzFrameAt g p B →
      E g p=a • (coordinateRicci g p - (1/2:ℝ) • coordinateScalarMetric g p)+c • g p

variable {Ω : Opens CoordinatePoint} {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem native_action_closed_source_unique_einstein_response
    (response : MetricFieldResponse) (core : AdmissibleMetricFirstResponseCore response)
    (d : NativeActionSourceData Ω F) (origin : (0:CoordinatePoint)∈Ω)
    (germ : C3NormalizedMetricGerm d.metric)
    (frame_near : ∀ᶠ p in 𝓝 0, ∃ B : CoordinatePoint ≃L[ℝ] CoordinatePoint, LorentzFrameAt d.metric p B)
    (gradient : coordinateScalarGradient d.metric≠0)
    (internal_equations : ∀ k, nativeActionDirectional (nativeMatterRestrictedAction d.action) k=0)
    (T : MetricField) (symmetric : MetricFieldSymmetric T)
    (regular : ∀ i j, DifferentiableAt ℝ (fun p => T p i j) 0)
    (densityRegular : ∀ i, ContDiff ℝ 1 (sourceDensityCoordinates (raisedSourceTensorDensity d.metric T) i))
    (represents : ∀ i φ, d.sourceDistribution i φ=
      ∫ p, sourceDensityCoordinates (raisedSourceTensorDensity d.metric T) i p * φ p)
    (κ : ℝ) (candidate_matching : response d.metric =ᶠ[𝓝 0] κ • T)
    (active_source : ∀ c : ℝ, κ • T 0 ≠ c • d.metric 0) :
    ∃! ac : ℝ × ℝ, ac.1≠0 ∧ CoordinateEinsteinResponseForm response ac.1 ac.2 := by
  obtain ⟨coeff,hcoeff,unique⟩ := admissible_c2_coordinate_metric_response_normal_form response core
  rcases coeff with ⟨a,b,c⟩
  have normal_near : response d.metric =ᶠ[𝓝 0]
      (a • coordinateRicci d.metric + b • coordinateScalarMetric d.metric + c • d.metric) := by
    filter_upwards [frame_near] with p hp
    obtain ⟨B,hB⟩ := hp
    exact hcoeff d.metric p B d.metricSymmetric
      (fun i j => (d.metricSmooth i j).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) hB
  have conserved := native_action_source_classical_covariant_conservation d origin
    (c3_normalized_metric_c2 d.metric germ) internal_equations T symmetric regular densityRegular represents
  have matching := normal_near.symm.trans candidate_matching
  have hdiv : coordinateDivergence d.metric
      (a • coordinateRicci d.metric+b • coordinateScalarMetric d.metric+c • d.metric) 0=0 := by
    rw [coordinate_divergence_germ_congruence d.metric _ _ matching,
      coordinateDivergence_smul_at_zero d.metric T κ regular,conserved,smul_zero]
  have hb := (c3_normal_geometric_coefficient_lock_iff d.metric germ gradient a b c).mp hdiv
  have hform : CoordinateEinsteinResponseForm response a c := by
    intro g p B hs hr hf
    rw [hcoeff g p B hs hr hf]
    exact MetricProjectionAudit.einstein_combination _ _ _ a b c hb
  have ha : a≠0 := by
    intro hz
    have hNF := normal_near.eq_of_nhds
    have hmatch := candidate_matching.eq_of_nhds
    change response d.metric 0=κ • T 0 at hmatch
    change response d.metric 0=a • coordinateRicci d.metric 0+b • coordinateScalarMetric d.metric 0+c • d.metric 0 at hNF
    have hzero : b=0 := by rw [hb,hz]; norm_num
    have hvalue : κ • T 0=c • d.metric 0 := by
      rw [← hmatch,hNF,hz,hzero]
      simp
    exact active_source c hvalue
  refine ⟨(a,c),⟨ha,hform⟩,?_⟩
  rintro ⟨a',c'⟩ ⟨_,other⟩
  have hother : ∀ (g : MetricField) (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
      (hs : MetricFieldSymmetric g) (hr : ∀ i j, ContDiffAt ℝ 2 (fun x => g x i j) p)
      (hf : LorentzFrameAt g p B),
      response g p=a' • coordinateRicci g p+(-a'/2) • coordinateScalarMetric g p+c' • g p := by
    intro g p B hs hr hf
    rw [other g p B hs hr hf]
    exact (MetricProjectionAudit.einstein_combination _ _ _ a' (-a'/2) c' rfl).symm
  have hu := unique (a',-a'/2,c') hother
  have hfirst : a'=a := congrArg Prod.fst hu
  have hlast : c'=c := congrArg (fun x : ℝ × ℝ × ℝ => x.2.2) hu
  exact Prod.ext hfirst hlast

theorem native_response_equation_normalization (g T : MetricField) (p : CoordinatePoint)
    (a c κ : ℝ) (active : a≠0)
    (matching : a • (coordinateRicci g p-(1/2:ℝ) • coordinateScalarMetric g p)+c • g p=κ • T p) :
    coordinateRicci g p-(1/2:ℝ) • coordinateScalarMetric g p+(c/a) • g p=(κ/a) • T p := by
  have h := congrArg (fun M : Tensor2 => (a⁻¹) • M) matching
  simpa only [smul_add,smul_smul,inv_mul_cancel₀ active,one_smul,← div_eq_inv_mul] using h

#print axioms native_action_closed_source_unique_einstein_response
#print axioms native_response_equation_normalization
end
end AASCSemanticExhaustion
