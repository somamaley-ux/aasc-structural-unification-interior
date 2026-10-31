import WickKGOriginalLFPath
import KGNativeWickUnitRepresentatives

/-! The ENTIRE normalized prequotient finite-action protocol family is fixed
before quotienting. All readouts, including failures, descend by actual phase
transport; no new source family is selected after taking rays. -/
noncomputable section
set_option maxHeartbeats 1000000
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem wick_KG_original_unit_core_ray_readout (a : Parameters) (s : ℝ)
    (u v : WickNonzeroCore) (unitu : ‖finiteParticleCoreToFock a u.val‖=1)
    (unitv : ‖finiteParticleCoreToFock a v.val‖=1) (same : wickCoreRaySetoid.r u v)
    {Ω : Opens CoordinatePoint} (π : WickKGOriginalProtocol Ω) :
    wickKGOriginalOutput a s u.val π=wickKGOriginalOutput a s v.val π := by
  obtain ⟨z,_,hv⟩ := same
  have normalized : ‖finiteParticleCoreToFock a (z • u.val)‖=1 := by rw [← hv];exact unitv
  have phase : ‖z‖=1 := by
    simpa only [map_smul,norm_smul,unitu,mul_one] using normalized
  rw [hv]
  exact (wick_KG_original_all_readouts_unit_phase a s z phase u.val π).symm

theorem wick_KG_original_normalized_prequotient_readouts (a : Parameters) (s : ℝ)
    (u v : WickNonzeroCore) (same : wickCoreRaySetoid.r u v)
    {Ω : Opens CoordinatePoint} (π : WickKGOriginalProtocol Ω) :
    wickKGOriginalOutput a s (originalWickUnitRepresentative a u.val) π=
      wickKGOriginalOutput a s (originalWickUnitRepresentative a v.val) π := by
  have sameUnit : wickCoreRaySetoid.r (originalWickUnitNonzeroRepresentative a u)
      (originalWickUnitNonzeroRepresentative a v) :=
    Quotient.exact ((original_wick_unit_representative_same_ray a u).trans
      ((Quotient.sound same).trans (original_wick_unit_representative_same_ray a v).symm))
  exact wick_KG_original_unit_core_ray_readout a s
    (originalWickUnitNonzeroRepresentative a u) (originalWickUnitNonzeroRepresentative a v)
    (original_wick_unit_representative_norm a u.val u.property)
    (original_wick_unit_representative_norm a v.val v.property) sameUnit π

def wickKGOriginalRayOutput (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    Quotient wickCoreRaySetoid → WickKGOriginalProtocol Ω → WickKGOriginalReadout :=
  Quotient.lift (fun u => wickKGOriginalOutput a s (originalWickUnitRepresentative a u.val)) (by
    intro u v same
    funext π
    exact wick_KG_original_normalized_prequotient_readouts a s u v same π)

def wickKGOriginalRayMetResp (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (ray : Quotient wickCoreRaySetoid) (H : MetricSourceProbe Ω) (z : ℝ) : Prop :=
  ∃ π,wickKGOriginalMetInc H π ∧ wickKGOriginalRayOutput a s Ω ray π=.first z

theorem wick_KG_original_normalized_prequotient_response_graph (a : Parameters) (s : ℝ)
    (u : WickNonzeroCore) (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω) (z : ℝ) :
    wickKGOriginalMetResp a s (originalWickUnitRepresentative a u.val) H z ↔
      originalWickRayMetricResponse a s Ω (Quotient.mk wickCoreRaySetoid u) H=z := by
  rw [wick_KG_original_response_graph]
  have h := original_wick_ray_source_is_actual_unit_response a s Ω u
  rw [h]

theorem wick_KG_original_ray_response_graph (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (ray : Quotient wickCoreRaySetoid) (H : MetricSourceProbe Ω) (z : ℝ) :
    wickKGOriginalRayMetResp a s Ω ray H z ↔ originalWickRayMetricResponse a s Ω ray H=z := by
  refine Quotient.inductionOn ray (fun u => ?_)
  change wickKGOriginalMetResp a s (originalWickUnitRepresentative a u.val) H z ↔ _
  exact wick_KG_original_normalized_prequotient_response_graph a s u Ω H z

end AASCKleinGordon
