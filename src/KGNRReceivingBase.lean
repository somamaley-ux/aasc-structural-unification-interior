import KGNRFullEnvelope

/-! Receiving realized questions obey the regional and time laws on evaluated
outputs. No literal identity of the original raw protocol syntax is asserted. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon
open KGQuantum W9 CategoryTheory TopologicalSpace AASCSemanticExhaustion
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

def kgNRRealizedRegion (a : Parameters) (s : ℝ) {Ω V : Opens CoordinatePoint}
    (h : Ω ≤ V) (A : KGNRObject a) (q : KGNRRealizedQuestion a s Ω A) :
    KGNRRealizedQuestion a s V A := by
  refine ⟨q.val,?_⟩
  obtain ⟨r,hr⟩ := q.prop
  refine ⟨kgNRQuestionExtend h r,?_⟩
  funext x
  rw [hr]
  exact (kg_nr_receiving_regional_record a s h A.shape x r).symm

theorem kg_nr_realized_region_identity (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGNRObject a) (q : KGNRRealizedQuestion a s Ω A) :
    kgNRRealizedRegion a s (le_refl Ω) A q = q := by apply Subtype.ext; rfl

theorem kg_nr_realized_region_composition (a : Parameters) (s : ℝ)
    {Ω V W : Opens CoordinatePoint} (h : Ω ≤ V) (k : V ≤ W)
    (A : KGNRObject a) (q : KGNRRealizedQuestion a s Ω A) :
    kgNRRealizedRegion a s (le_trans h k) A q =
      kgNRRealizedRegion a s k A (kgNRRealizedRegion a s h A q) := by apply Subtype.ext; rfl

theorem kg_nr_realized_region_arrow (a : Parameters) (s : ℝ)
    {Ω V : Opens CoordinatePoint} (h : Ω ≤ V) {A B : KGNRObject a}
    (f : A ⟶ B) (q : KGNRRealizedQuestion a s Ω B) :
    kgNRRealizedRegion a s h A (kgNRRealizedPullback a s Ω f q) =
      kgNRRealizedPullback a s V f (kgNRRealizedRegion a s h B q) := by apply Subtype.ext; rfl

theorem kg_nr_realized_region_flow (a : Parameters) (s t : ℝ)
    {Ω V : Opens CoordinatePoint} (h : Ω ≤ V) (A : KGNRObject a)
    (q : KGNRRealizedQuestion a s Ω A) :
    kgNRRealizedRegion a s h A (kgNRRealizedFlow a s Ω t A q) =
      kgNRRealizedFlow a s V t A (kgNRRealizedRegion a s h A q) := by apply Subtype.ext; rfl

theorem kg_nr_realized_flow_zero (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGNRObject a) (q : KGNRRealizedQuestion a s Ω A) :
    kgNRRealizedFlow a s Ω 0 A q = q := by
  apply Subtype.ext
  funext x
  exact congrArg q.val (kg_nr_spatial_family_pure_zero a A.shape x)

theorem kg_nr_realized_flow_add (a : Parameters) (s t u : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGNRObject a) (q : KGNRRealizedQuestion a s Ω A) :
    kgNRRealizedFlow a s Ω (t+u) A q =
      kgNRRealizedFlow a s Ω u A (kgNRRealizedFlow a s Ω t A q) := by
  apply Subtype.ext
  funext x
  exact congrArg q.val (kg_nr_spatial_family_pure_add a t u A.shape x)

end AASCKleinGordon
