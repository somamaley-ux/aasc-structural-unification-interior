import KGWeylRelations

noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem weylCoherentImage_continuous (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    Continuous (fun g : 𝓢(Momentum,ℂ) => weylCoherentImage a g f) := by
  unfold weylCoherentImage
  apply Continuous.smul
  · apply Complex.continuous_exp.comp
    apply Continuous.sub
    · exact Complex.continuous_ofReal.comp
        (((oneParticleSchwartzToHilbert a).continuous.norm.pow 2).div_const 2) |>.neg
    · exact (continuous_inner.comp
        ((oneParticleSchwartzToHilbert a).continuous.prodMk continuous_const))
  · exact (exponentialVector_continuous a).comp (continuous_const.add continuous_id)

theorem weylOperator_span_orbit_continuous (a : Parameters) (u : coherentSpan a) :
    Continuous (fun g : 𝓢(Momentum,ℂ) => weylOperator a g (u : FockHilbert a)) := by
  obtain ⟨v,⟨c,rfl⟩⟩:=u
  simp only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul]
  apply continuous_finset_sum
  intro f _
  simpa only [weylOperator_exponentialVector] using
    (continuous_const.smul (weylCoherentImage_continuous a f) :
      Continuous (fun g : 𝓢(Momentum,ℂ) => c f • weylCoherentImage a g f))

theorem weylOperator_strongly_continuous (a : Parameters) (v : FockHilbert a) :
    Continuous (fun g : 𝓢(Momentum,ℂ) => weylOperator a g v) :=
  continuous_isometric_orbits_of_dense_topological (fun g => weylOperator a g)
    (fun g => (weylUnitary a g).isometry) (coherentSpan a).subtypeL
    (coherentSpan_subtype_dense a) (weylOperator_span_orbit_continuous a) v

theorem weylOperator_jointly_continuous (a : Parameters) :
    Continuous (fun p : 𝓢(Momentum,ℂ) × FockHilbert a => weylOperator a p.1 p.2) :=
  continuous_isometric_action_of_orbits (fun g => weylOperator a g)
    (fun g => (weylUnitary a g).isometry) (weylOperator_strongly_continuous a)

end AASCKleinGordon
