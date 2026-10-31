import KernelFaithfulCurvedKGEndpoints
import EHKGFlatLocalRecovery
import EHKGCentralSupportSystem

/-! Source-contract completion of the preserved 46-field candidate. This
successor retains that exact proof and adds the explicit original-mass H=0
uniqueness receiver and central compact support system requested in review.
Compiled audit/replay and independent acceptance remain external obligations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

structure CompleteKernelFaithfulCurvedKGEndpoints (a : Parameters) (s : ℝ) : Prop
    extends KernelFaithfulCurvedKGEndpoints a s where
  flat_local_uniqueness : ∀ (f h : CurvedCauchyDatum a) (v : CoordinatePoint → ℝ),
    ContDiffOn ℝ (⊤ : ℕ∞) v (protectedDiamond (conformalFrequency a)) →
    (∀ p ∈ protectedDiamond (conformalFrequency a),
      scalarFieldWaveOperator (originalEHActMetric (0 : MetricSourceProbe (⊤ : Opens CoordinatePoint))) v p =
        (massWaveNumber a) ^ 2 * v p) →
    (∀ x ∈ centralLeafDomain (conformalFrequency a), v (centralLeafPoint x) = f x) →
    (∀ x ∈ centralLeafDomain (conformalFrequency a), scalarPartial v (centralLeafPoint x) 0 = h x) →
      EqOn v (compactFlatField a (centralLeafDomain (conformalFrequency a)) f h) (protectedDiamond (conformalFrequency a))
  central_support_exact : ∀ f h : CurvedCauchyDatum a,
    tsupport (fun x => compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h (centralLeafPoint x)) = tsupport f ∧
    tsupport (fun x => actualNormalDerivative (conformalFrequency a)
      (compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h) (centralLeafPoint x)) = tsupport h
  compact_support_system : ∀ f h : CurvedCauchyDatum a,
    IsCompact (tsupport f ∪ tsupport h) ∧
    tsupport f ∪ tsupport h ⊆ centralLeafDomain (conformalFrequency a) ∧
    tsupport (compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h) ∩
      protectedDiamond (conformalFrequency a) ⊆ metricCausalShadow (conformalFrequency a) (tsupport f ∪ tsupport h)

theorem kernel_faithful_same_eh_curved_kg_complete (a : Parameters) (s : ℝ) :
    CompleteKernelFaithfulCurvedKGEndpoints a s where
  toKernelFaithfulCurvedKGEndpoints := kernel_faithful_same_eh_curved_kg a s
  flat_local_uniqueness := fixed_mass_flat_local_cauchy_unique a
  central_support_exact := central_cauchy_trace_support_exact a
  compact_support_system := retained_compact_cauchy_support_system a

end AASCKleinGordon.CurvedKG
