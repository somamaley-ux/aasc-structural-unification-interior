import EHKGLFEvolutionContinuity
import EHKGDiamondDomain

/-! Restriction to the local smooth compact-open topology. The topology
observes only compact sets inside the open domain. All jets agree when local
histories agree there, regardless of their outside values. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

def LocalSmoothRealField (D : Opens CoordinatePoint) :=
  {F : CoordinatePoint → ℝ // ContDiffOn ℝ (⊤ : ℕ∞) F D}

def InternalCompact (D : Opens CoordinatePoint) :=
  {K : Compacts CoordinatePoint // (K : Set CoordinatePoint) ⊆ D}

def localSmoothRealJet (D : Opens CoordinatePoint) (F : LocalSmoothRealField D)
    (n : ℕ) (K : InternalCompact D) :
    C(K.val, ContinuousMultilinearMap ℝ (fun _ : Fin n => CoordinatePoint) ℝ) := by
  have withinContinuous := F.property.continuousOn_iteratedFDerivWithin
    (m := n) (by exact_mod_cast le_top) D.isOpen.uniqueDiffOn
  have actualContinuous : ContinuousOn (iteratedFDeriv ℝ n F.val) D :=
    withinContinuous.congr (fun p hp => (iteratedFDerivWithin_of_isOpen n D.isOpen hp).symm)
  exact ⟨fun p => iteratedFDeriv ℝ n F.val p,
    continuousOn_iff_continuous_restrict.mp (actualContinuous.mono K.property)⟩

def localSmoothRealJetEmbedding (D : Opens CoordinatePoint) (F : LocalSmoothRealField D) :
    (n : ℕ) → (K : InternalCompact D) →
      C(K.val, ContinuousMultilinearMap ℝ (fun _ : Fin n => CoordinatePoint) ℝ) :=
  fun n K => localSmoothRealJet D F n K

instance localSmoothRealFieldTopology (D : Opens CoordinatePoint) :
    TopologicalSpace (LocalSmoothRealField D) :=
  TopologicalSpace.induced (localSmoothRealJetEmbedding D) inferInstance

def smoothGlobalRestriction (D : Opens CoordinatePoint) (F : SmoothRealGlobalField) :
    LocalSmoothRealField D := ⟨F.val, F.property.contDiffOn⟩

theorem smooth_global_restriction_continuous (D : Opens CoordinatePoint) :
    Continuous (smoothGlobalRestriction D) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro n
  apply continuous_pi
  intro K
  have embeddingContinuous : Continuous smoothRealGlobalJetEmbedding := continuous_induced_dom
  have h := (continuous_apply K.val).comp ((continuous_apply n).comp embeddingContinuous)
  convert h using 1

theorem local_jets_extension_independent (D : Opens CoordinatePoint)
    (F G : LocalSmoothRealField D) (same : EqOn F.val G.val D)
    (n : ℕ) (K : InternalCompact D) : localSmoothRealJet D F n K = localSmoothRealJet D G n K := by
  apply ContinuousMap.ext
  intro p
  have near : F.val =ᶠ[𝓝 (p : CoordinatePoint)] G.val := by
    filter_upwards [D.isOpen.mem_nhds (K.property p.property)] with q hq
    exact same hq
  exact (near.iteratedFDeriv ℝ n).eq_of_nhds

def compactCurvedLocalEvolution (a : Parameters)
    (data : TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞) ×
      TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞)) :
    LocalSmoothRealField ⟨protectedDiamond (conformalFrequency a), protected_diamond_open _⟩ :=
  smoothGlobalRestriction _ (compactCurvedSmoothEvolution a (centralLeafDomain (conformalFrequency a)) data)

theorem compact_curved_local_evolution_lf_continuous (a : Parameters) :
    Continuous (compactCurvedLocalEvolution a) :=
  (smooth_global_restriction_continuous _).comp
    (compact_curved_evolution_lf_to_smooth_compact_open a (centralLeafDomain (conformalFrequency a)))

end AASCKleinGordon.CurvedKG
