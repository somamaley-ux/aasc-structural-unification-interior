import WickGraphSeminormDomination
import WickNativeJointCoreContinuity

noncomputable section
set_option maxHeartbeats 8000000
open scoped SchwartzMap NNReal DirectSum BoundedContinuousFunction
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickJetGraphNormFamily (σ : WickJetGraphIndex) : Seminorm ℂ FiniteParticleCore :=
  (normSeminorm ℂ (WickJetGraphSpace σ)).comp (wickJetGraphCLM σ).toLinearMap

lemma wick_jet_graph_norm_family_continuous (σ : WickJetGraphIndex) :
    Continuous (wickJetGraphNormFamily σ) := (wickJetGraphCLM σ).continuous.norm

/-- The independently fixed jet graph family generates the ORIGINAL topology.
Both domination directions are proved using actual graph operators. -/
theorem wick_jet_graph_withSeminorms : WithSeminorms wickJetGraphNormFamily := by
  apply finiteParticleCore_withSeminorms.congr
  · intro σ
    obtain ⟨S,C,hC,hb⟩ := Seminorm.bound_of_continuous finiteParticleCore_withSeminorms
      (wickJetGraphNormFamily σ) (wick_jet_graph_norm_family_continuous σ)
    exact ⟨S,C,hb⟩
  · intro p
    refine ⟨{wickCoreDominatingGraphIndex p},1,?_⟩
    rw [one_smul,Finset.sup_singleton]
    exact wick_core_seminorm_le_graph_norm p

/-- Actual initial topology of all jet graph operators plus the original Fock
inclusion. This declares a Banach-valued graph realization of the source core. -/
def wickDeclaredGraphTopology (a : Parameters) : TopologicalSpace FiniteParticleCore :=
  (⨅ σ : WickJetGraphIndex,TopologicalSpace.induced (wickJetGraphCLM σ) inferInstance) ⊓
    TopologicalSpace.induced (finiteParticleCoreToFock a) inferInstance

def wickJetGraphSigmaEquiv : ((σ : WickJetGraphIndex) × Fin 1) ≃ WickJetGraphIndex where
  toFun := fun x => x.1
  invFun := fun σ => ⟨σ,0⟩
  left_inv := by
    rintro ⟨σ,j⟩
    have hj : j=0 := Subsingleton.elim _ _
    cases hj
    rfl
  right_inv := fun _ => rfl

lemma wick_jet_initial_topology_eq_original :
    (⨅ σ : WickJetGraphIndex,TopologicalSpace.induced (wickJetGraphCLM σ) inferInstance)=
      (inferInstance : TopologicalSpace FiniteParticleCore) := by
  have hi := withSeminorms_iInf (𝕜:=ℂ) (E:=FiniteParticleCore)
    (κ:=fun _ : WickJetGraphIndex => Fin 1)
    (p:=fun σ => SeminormFamily.comp (fun _ : Fin 1 => normSeminorm ℂ (WickJetGraphSpace σ))
      (wickJetGraphCLM σ).toLinearMap)
    (t:=fun σ => TopologicalSpace.induced (wickJetGraphCLM σ) inferInstance)
    (fun σ : WickJetGraphIndex =>
    LinearMap.withSeminorms_induced (norm_withSeminorms ℂ (WickJetGraphSpace σ))
      (wickJetGraphCLM σ).toLinearMap)
  have ho := wick_jet_graph_withSeminorms.congr_equiv wickJetGraphSigmaEquiv
  have hei := WithSeminorms.withSeminorms_eq
    (t:=⨅ σ : WickJetGraphIndex,TopologicalSpace.induced (wickJetGraphCLM σ) inferInstance) hi
  have heo := WithSeminorms.withSeminorms_eq
    (t:=(inferInstance : TopologicalSpace FiniteParticleCore)) ho
  exact hei.trans heo.symm

/-- Exact graph/LF compatibility, proved without assuming the response continuous
for a newly chosen weaker topology. -/
theorem wick_declared_graph_topology_eq_original (a : Parameters) :
    wickDeclaredGraphTopology a=(inferInstance : TopologicalSpace FiniteParticleCore) := by
  rw [wickDeclaredGraphTopology,wick_jet_initial_topology_eq_original]
  apply inf_eq_left.mpr
  exact continuous_iff_le_induced.mp (finiteParticleCoreToFock_continuous a)

theorem original_wick_native_response_joint_graph_continuous
    (a : Parameters) (s : ℝ) (Ω : Opens (Fin 4 → ℝ)) :
    letI : TopologicalSpace FiniteParticleCore := wickDeclaredGraphTopology a
    Continuous (fun z : (FiniteParticleCore × FiniteParticleCore) × MetricSourceProbe Ω =>
      originalWickNativeMetricResponse a s z.1.1 z.1.2 Ω z.2) := by
  simpa only [wick_declared_graph_topology_eq_original] using
    original_wick_native_response_joint_core_continuous a s Ω

end AASCKleinGordon
