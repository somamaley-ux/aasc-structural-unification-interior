import KGNativeWickOperationalIncidence
import KGNativeWickUnitRepresentatives
import KGNativeWickUniformTestBound

/-! Bounded prequotient operational sources on actual unit-ray evaluations
and straight compact metric protocols. Arbitrary protocol completeness and
joint graph-to-strong-dual attachment are not inferred from this assembly. -/
noncomputable section
set_option maxHeartbeats 8000000
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

def originalWickRayLinearMetricIncidence (a : Parameters) (s : ℝ) (Ω : Opens (Fin 4 → ℝ))
    (ray : Quotient wickCoreRaySetoid) : OperationalMetricIncidence Ω (MetricSourceProbe Ω) :=
  originalWickNativeLinearMetricIncidence a s (originalWickUnitRepresentative a ray.out.val) Ω

theorem original_wick_ray_straight_operational_response (a : Parameters) (s : ℝ)
    (Ω : Opens (Fin 4 → ℝ)) (ray : Quotient wickCoreRaySetoid) (H : MetricSourceProbe Ω) :
    operationalMetricResponse (originalWickRayLinearMetricIncidence a s Ω ray) H=
      originalWickRayMetricResponse a s Ω ray H := by
  unfold originalWickRayLinearMetricIncidence
  rw [original_wick_operational_response_is_actual_response]
  have hu := original_wick_ray_source_is_actual_unit_response a s Ω ray.out
  rw [Quotient.out_eq] at hu
  exact (congrArg (fun W : MetricSourceProbe Ω →L[ℝ] ℝ => W H) hu).symm

theorem original_wick_ray_operational_compact_continuity (a : Parameters) (s : ℝ)
    (Ω : Opens (Fin 4 → ℝ)) (ray : Quotient wickCoreRaySetoid)
    (K : Compacts (Fin 4 → ℝ)) (hK : (K : Set (Fin 4 → ℝ)) ⊆ Ω) :
    Continuous (operationalMetricResponse (originalWickRayLinearMetricIncidence a s Ω ray) ∘
      TestFunction.ofSupportedIn hK) := by
  have heq : operationalMetricResponse (originalWickRayLinearMetricIncidence a s Ω ray)=
      originalWickRayMetricResponse a s Ω ray :=
    funext (original_wick_ray_straight_operational_response a s Ω ray)
  rw [heq]
  exact (originalWickRayMetricResponse a s Ω ray).continuous.comp (TestFunction.continuous_ofSupportedIn hK)

theorem original_wick_ray_operational_functional_is_same_source (a : Parameters) (s : ℝ)
    (Ω : Opens (Fin 4 → ℝ)) (ray : Quotient wickCoreRaySetoid) :
    operationalMetricFunctional (originalWickRayLinearMetricIncidence a s Ω ray)
      (original_wick_ray_operational_compact_continuity a s Ω ray)=
        originalWickRayMetricResponse a s Ω ray := by
  ext H
  exact original_wick_ray_straight_operational_response a s Ω ray H

theorem original_wick_native_response_common_L1_bound (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ)) (H : MetricSourceProbe Ω) :
    ‖originalWickNativeMetricResponse a s u v Ω H‖≤
      (1/2 : ℝ)*originalWickTotalStateBound a s u v*wickMetricTestL1 (nativeToWickMetricTest Ω H) := by
  rw [original_wick_native_metric_response_half_pairing,norm_mul]
  have hb := original_wick_metric_distribution_common_L1_bound a s u v (nativeToWickMetricTest Ω H)
  have hn : ‖(1/2 : ℂ)‖=(1/2 : ℝ) := by norm_num
  rw [hn]
  exact (mul_le_mul_of_nonneg_left hb (by norm_num)).trans_eq (by ring)

end AASCKleinGordon
