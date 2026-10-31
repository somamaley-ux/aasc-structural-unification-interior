import KGRawTensorCoherence
import KGOriginalQuantumContinuation

/-! Constructed quotient operations on the actual comparison family.
This file does not rename the still incomplete six-coordinate original QP
certificate as a premise or claim the full corpus endpoint. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open scoped TensorProduct
open KGQuantum TopologicalSpace AASCSemanticExhaustion
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem kg_raw_orbit_map_continuous : Continuous (rayMap E) := by
  change Continuous (Quotient.mk (pureVectorSetoid E))
  exact continuous_quotient_mk'

def kgTensorRay : PhysicalRay E → PhysicalRay F → PhysicalRay (E ⊗[ℂ] F) :=
  Quotient.lift₂ (fun x y => rayMap _ (kgRawTensor x y)) (by
    intro x y x' y' hx hy
    obtain ⟨c,hc,hx⟩ := hx
    obtain ⟨d,hd,hy⟩ := hy
    apply (rayMap_eq_iff _ _ _).mpr
    refine ⟨c*d,mul_ne_zero hc hd,?_⟩
    have product : (c • x.val) ⊗ₜ[ℂ] (d • y.val) = (c*d) • (x.val ⊗ₜ[ℂ] y.val) :=
      congrArg Subtype.val (kg_raw_tensor_scalar_equivariance c d hc hd x y)
    exact product.symm.trans (congrArg₂ (fun v w => v ⊗ₜ[ℂ] w) hx hy))

theorem kg_tensor_ray_weights (r t : PhysicalRay E) (s u : PhysicalRay F) :
    rayTransitionProbability (kgTensorRay r s) (kgTensorRay t u) =
      rayTransitionProbability r t * rayTransitionProbability s u := by
  induction r using Quotient.inductionOn with | _ x =>
    induction t using Quotient.inductionOn with | _ z =>
      induction s using Quotient.inductionOn with | _ y =>
        induction u using Quotient.inductionOn with | _ w =>
          exact kg_raw_tensor_weights_multiply x z y w

section TensorContinuation
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

theorem kg_tensor_ray_continuation (a : Parameters) (q : ProperPoincareTransform)
    (A B : KGComparisonObject) (r : PhysicalRay (KGComparisonCarrier a A))
    (s : PhysicalRay (KGComparisonCarrier a B)) :
    unitaryRayMap (kgComparisonPoincare a q (.tensor A B)) (kgTensorRay r s) =
      kgTensorRay (unitaryRayMap (kgComparisonPoincare a q A) r)
        (unitaryRayMap (kgComparisonPoincare a q B) s) := by
  induction r using Quotient.inductionOn with | _ x =>
    induction s using Quotient.inductionOn with | _ y =>
      exact congrArg (rayMap _) (kg_comparison_continuation_monoidal a q A B x y)

end TensorContinuation

theorem kg_descended_continuation_unique (U : E ≃ₗᵢ[ℂ] E) :
    ∃! C : PhysicalRay E → PhysicalRay E,
      ∀ x,C (rayMap E x)=rayMap E (PureVector.mapUnitary U x) := by
  refine ⟨unitaryRayMap U,by intro x; rfl,?_⟩
  intro C hC
  funext r
  induction r using Quotient.inductionOn with | _ x => exact hC x

theorem kg_original_quantum_readout_exact (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u : WickNonzeroCore) (π : WickMetricPathRoleProtocol Ω) :
    wickIdentifiedMetricPathRecordReadout a s Ω
      (kgOriginalQuantumRecord a s Ω (rayMap _ (kgRawOriginalEquiv a u))) π =
        wickMetricPathRoleOutput a s Ω u π := by
  rw [kg_original_quantum_record_on_representatives]
  rfl

theorem kg_original_quantum_finite_failure (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u : WickNonzeroCore) (H : MetricSourceProbe Ω)
    (outside : H ∉ wickOriginalMetricNeighborhood Ω) :
    wickIdentifiedMetricPathRecordReadout a s Ω
      (kgOriginalQuantumRecord a s Ω (rayMap _ (kgRawOriginalEquiv a u)))
        (.original (.metric (.finite H))) = .metric .failed := by
  rw [kg_original_quantum_readout_exact]
  exact wick_metric_path_finite_failure_retained a s Ω u H outside

theorem kg_original_quantum_born_comparison (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u v : WickNonzeroCore) (g : ProperPoincareTransform) :
    wickIdentifiedMetricPathRecordReadout a s Ω
      (kgOriginalQuantumRecord a s Ω (rayMap _ (kgRawOriginalEquiv a u)))
        (.original (.comparison g v)) = .probability (wickOriginalRoleComparison a u v g) := by
  rw [kg_original_quantum_readout_exact]
  rfl

end AASCKleinGordon
