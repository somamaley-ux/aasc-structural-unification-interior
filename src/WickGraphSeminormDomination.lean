import WickSectorJetGraphOperators

noncomputable section
set_option maxHeartbeats 8000000
open scoped SchwartzMap NNReal DirectSum BoundedContinuousFunction
namespace AASCKleinGordon

lemma wick_core_sector_finite_jet_control (p : CoreSeminormIndex) (n : ℕ) :
    ∃ J : Finset (ℕ × ℕ), ∃ C : NNReal, ∀ f : bosonicSchwartz n,
      p.val (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n f) ≤
        (C : ℝ) * J.sup (schwartzSeminormFamily ℂ (ParticleConfiguration n) ℂ) f.val := by
  have hs := Topology.IsInducing.withSeminorms
    (f:=(bosonicSchwartz n).subtype)
    (schwartz_withSeminorms ℂ (ParticleConfiguration n) ℂ) Topology.IsInducing.subtypeVal
  obtain ⟨J,C,hC,hb⟩ := Seminorm.bound_of_continuous hs
    (p.val.comp (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n)) (p.property n)
  refine ⟨J,C,fun f => ?_⟩
  have h := hb f
  rw [← SeminormFamily.finset_sup_comp] at h
  exact h

/-- The graph index is selected from the ORIGINAL generating seminorm, not from
any response, stress tensor or desired continuity conclusion. -/
def wickCoreDominatingGraphIndex (p : CoreSeminormIndex) : WickJetGraphIndex where
  jets n := Classical.choose (wick_core_sector_finite_jet_control p n)
  weights n := Classical.choose (Classical.choose_spec (wick_core_sector_finite_jet_control p n))

lemma wick_core_dominating_graph_sector_bound (p : CoreSeminormIndex) (n : ℕ)
    (f : bosonicSchwartz n) :
    p.val (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n f) ≤
      ((wickCoreDominatingGraphIndex p).weights n : ℝ) *
        ((wickCoreDominatingGraphIndex p).jets n).sup
          (schwartzSeminormFamily ℂ (ParticleConfiguration n) ℂ) f.val :=
  Classical.choose_spec (Classical.choose_spec (wick_core_sector_finite_jet_control p n)) f

lemma wick_seminorm_finset_sum_le {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    (p : Seminorm ℂ V) (S : Finset ι) (f : ι → V) :
    p (∑ i ∈ S,f i) ≤ ∑ i ∈ S,p (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi hS =>
    simp only [Finset.sum_insert hi]
    exact (map_add_le_add p _ _).trans (add_le_add le_rfl hS)

/-- Every ORIGINAL generating seminorm is bounded by an actual jet graph
operator norm. Finite particle support, not a response cutoff limit, is used. -/
theorem wick_core_seminorm_le_graph_norm (p : CoreSeminormIndex) (u : FiniteParticleCore) :
    p.val u ≤ ‖wickJetGraphCLM (wickCoreDominatingGraphIndex p) u‖ := by
  classical
  let σ := wickCoreDominatingGraphIndex p
  let q : ∀ n,Seminorm ℂ 𝓢(ParticleConfiguration (n+0),ℂ) :=
    fun n => σ.weights n • (σ.jets n).sup (schwartzSeminormFamily ℂ (ParticleConfiguration n) ℂ)
  have hs : Summable (fun n => (σ.weights n : ℝ)*
      (σ.jets n).sup (schwartzSeminormFamily ℂ (ParticleConfiguration n) ℂ) (u n).val) := by
    simpa only [Seminorm.smul_apply,NNReal.smul_def,smul_eq_mul,Nat.add_zero] using
      wick_core_shift_seminorm_summable 0 q u
  calc
    p.val u = p.val (∑ n ∈ u.support,DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n (u n)) := by
      congr 1
      simpa only [DirectSum.lof_eq_of] using (DirectSum.sum_support_of u).symm
    _ ≤ ∑ n ∈ u.support,p.val (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n (u n)) :=
      wick_seminorm_finset_sum_le _ _ _
    _ ≤ ∑ n ∈ u.support,(σ.weights n : ℝ)*
        (σ.jets n).sup (schwartzSeminormFamily ℂ (ParticleConfiguration n) ℂ) (u n).val := by
      apply Finset.sum_le_sum
      intro n hn
      exact wick_core_dominating_graph_sector_bound p n (u n)
    _ ≤ ∑' n,(σ.weights n : ℝ)*
        (σ.jets n).sup (schwartzSeminormFamily ℂ (ParticleConfiguration n) ℂ) (u n).val :=
      hs.sum_le_tsum _ (fun n _ => mul_nonneg (σ.weights n).coe_nonneg (apply_nonneg _ _))
    _ = ‖wickJetGraphCLM σ u‖ := (wick_jet_graph_norm σ u).symm

end AASCKleinGordon
