import OriginalEHMetricActGeometry
import CompactMetricSourceRepresentation
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! An actual compact smooth original EH operand, with a controlled polynomial
germ at the origin. Curvature and Cauchy geometry are separate subsequent proofs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

def curvatureBump : ContDiffBump (0 : CoordinatePoint) := default

def curvatureSeedProfile (p : CoordinatePoint) : ℝ := curvatureBump p * (p 0) ^ 2

theorem curvature_seed_profile_smooth :
    ContDiff ℝ (⊤ : ℕ∞) curvatureSeedProfile :=
  curvatureBump.contDiff.mul
    ((ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ).contDiff.pow 2)

theorem curvature_seed_profile_compact : HasCompactSupport curvatureSeedProfile :=
  curvatureBump.hasCompactSupport.mul_right

def curvatureSeedScalar : ScalarSourceProbe (⊤ : Opens CoordinatePoint) :=
  ⟨curvatureSeedProfile, curvature_seed_profile_smooth, curvature_seed_profile_compact,
    fun _ _ => Set.mem_univ _⟩

def curvatureSeedOperand : MetricSourceProbe (⊤ : Opens CoordinatePoint) :=
  sourceTestInsertion 4 curvatureSeedScalar

def curvedOperand (epsilon : ℝ) : MetricSourceProbe (⊤ : Opens CoordinatePoint) :=
  epsilon • curvatureSeedOperand

theorem curvature_seed_profile_near_zero :
    curvatureSeedProfile =ᶠ[𝓝 (0 : CoordinatePoint)] (fun p => (p 0) ^ 2) := by
  filter_upwards [curvatureBump.eventuallyEq_one] with p hp
  simp only [curvatureSeedProfile, hp, Pi.one_apply, one_mul]

theorem curved_operand_component (epsilon : ℝ) (p : CoordinatePoint) (i : Fin 10) :
    curvedOperand epsilon p i = if i = 4 then epsilon * curvatureSeedProfile p else 0 := by
  change epsilon * ((sourceCoordinateInsertion 4) (curvatureSeedScalar p) i) = _
  by_cases same : i = 4 <;> simp [sourceCoordinateInsertion, curvatureSeedScalar, same]

theorem curved_operand_metric_component (epsilon : ℝ) (p : CoordinatePoint) (i j : Fin 4) :
    originalEHActMetric (curvedOperand epsilon) p i j =
      metric i j + (if i = 1 ∧ j = 1 then epsilon * curvatureSeedProfile p else 0) := by
  change wickNativeFlatMetric p i j + tensorEncode (curvedOperand epsilon p) i j = _
  rw [original_eh_native_flat_value]
  congr 1
  fin_cases i <;> fin_cases j <;> simp [tensorEncode, curved_operand_component]

def curvaturePolynomialMetric (epsilon : ℝ) : MetricField :=
  fun p i j => metric i j + if i = 1 ∧ j = 1 then epsilon * (p 0) ^ 2 else 0

theorem curved_operand_metric_near_polynomial (epsilon : ℝ) :
    originalEHActMetric (curvedOperand epsilon) =ᶠ[𝓝 (0 : CoordinatePoint)]
      curvaturePolynomialMetric epsilon := by
  filter_upwards [curvature_seed_profile_near_zero] with p hp
  funext i j
  rw [curved_operand_metric_component]
  simp only [curvaturePolynomialMetric, hp]

theorem curved_operand_eventually_admitted :
    ∀ᶠ epsilon : ℝ in 𝓝 0,
      curvedOperand epsilon ∈ wickOriginalMetricNeighborhood (⊤ : Opens CoordinatePoint) :=
  wick_original_metric_neighborhood_all_directions _ curvatureSeedOperand

theorem exists_positive_curved_operand_admitted :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      curvedOperand epsilon ∈ wickOriginalMetricNeighborhood (⊤ : Opens CoordinatePoint) := by
  obtain ⟨radius, positive, inside⟩ :=
    Metric.mem_nhds_iff.mp curved_operand_eventually_admitted
  refine ⟨radius / 2, by positivity, inside ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < radius / 2)]
  linarith

end AASCKleinGordon.CurvedKG
