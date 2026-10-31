import KGNRSourceCoreFlow

/-! Q19 is proved on actual original preparations, using compact smooth tests
at two momentum points. It is not a declared nontriviality certificate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory
open scoped SchwartzMap ContDiff
namespace AASCKleinGordon

theorem kg_nr_exists_schwartz_at (p : Momentum) :
    ∃ f : 𝓢(Momentum,ℂ),f p = 1 := by
  obtain ⟨f,_,hc,hs,_,hp⟩ := exists_contDiff_tsupport_subset
    (E := Momentum) (x := p) (n := ⊤) (s := Set.univ) (by simp)
  have hcc : HasCompactSupport (fun x => (f x : ℂ)) :=
    hc.comp_left (g := Complex.ofReal) (by simp)
  exact ⟨hcc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hs),
    by simpa using congrArg Complex.ofReal hp⟩

theorem kg_nr_source_not_homogeneous (a : Parameters) (c : ℂ) :
    ¬ ∀ x : kgOriginalOneCore a,kgNROriginalOneCoreKinetic a x = c • x := by
  intro h
  have allp (p : Momentum) : (kgNRKineticEnergy a p : ℂ) = c := by
    obtain ⟨f,hf⟩ := kg_nr_exists_schwartz_at p
    have hx := h (kgOriginalOneCoreOfSchwartz a f)
    unfold kgNROriginalOneCoreKinetic at hx
    rw [kg_original_one_core_coordinates_of_schwartz] at hx
    have he : kgOriginalOneCoreOfSchwartz a (kgNRSchwartzKinetic a f) =
        kgOriginalOneCoreOfSchwartz a (c • f) :=
      hx.trans ((kgOriginalOneCoreSchwartzEquiv a).map_smul c f).symm
    have hm := (kgOriginalOneCoreSchwartzEquiv a).injective he
    have hp := congrArg (fun g : 𝓢(Momentum,ℂ) => g p) hm
    simpa only [kg_nr_schwartz_kinetic_apply,SchwartzMap.smul_apply,
      smul_eq_mul,hf,mul_one] using hp
  have h0 : c = 0 := by simpa [kgNRKineticEnergy,momentumSq] using (allp 0).symm
  have hp := allp ![1,0,0]
  have hpos : 0 < kgNRKineticEnergy a ![1,0,0] := by
    simpa [kgNRKineticEnergy,momentumSq] using
      div_pos (show (0 : ℝ) < 1 by norm_num) (mul_pos (show (0 : ℝ) < 2 by norm_num) a.mass_pos)
  exact (Complex.ofReal_ne_zero.mpr hpos.ne') (hp.trans h0)

theorem kg_nr_spatial_generator_not_homogeneous (a : Parameters) (c : ℂ) :
    ∃ f : (kgNRSpatialKinetic a).domain,kgNRSpatialKinetic a f ≠ c • f.val := by
  by_contra h
  push_neg at h
  apply kg_nr_source_not_homogeneous a c
  intro x
  have hg := kg_nr_original_one_core_spatial_graph a x
  let f : (kgNRSpatialKinetic a).domain :=
    ⟨kgOriginalOneCoreSpatialEmbedding a x,LinearPMap.mem_domain_of_mem_graph hg⟩
  have he : kgNRSpatialKinetic a f =
      kgOriginalOneCoreSpatialEmbedding a (kgNROriginalOneCoreKinetic a x) := by
    obtain ⟨y,hy,hk⟩ := (LinearPMap.mem_graph_iff _).mp hg
    have hyf : y = f := Subtype.ext hy
    exact (congrArg (kgNRSpatialKinetic a) hyf).symm.trans hk
  apply (kgOriginalOneCoreSpatialEmbedding a).injective
  calc
    _ = kgNRSpatialKinetic a f := he.symm
    _ = c • f.val := h f
    _ = _ := ((kgOriginalOneCoreSpatialEmbedding a).map_smul c x).symm

end AASCKleinGordon
