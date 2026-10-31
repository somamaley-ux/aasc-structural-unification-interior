import KGNativeWickRayOperationalSource
import KGNativeWickQuadraticExtension

noncomputable section
set_option maxHeartbeats 8000000
open scoped SchwartzMap DirectSum NNReal
namespace AASCKleinGordon

def wickCoreSchwartzProjectionLM (n : ℕ) : FiniteParticleCore →ₗ[ℂ] 𝓢(ParticleConfiguration n,ℂ) :=
  (bosonicSchwartz n).subtype.comp (DirectSum.component ℂ ℕ (fun m => bosonicSchwartz m) n)

lemma wick_core_schwartz_projection_continuous (n : ℕ) :
    Continuous (wickCoreSchwartzProjectionLM n) := by
  apply Seminorm.continuous_of_continuous_comp (schwartz_withSeminorms ℂ (ParticleConfiguration n) ℂ)
  intro i
  apply core_continuous_seminorm_of_sector_continuous
  intro m
  by_cases hm : m=n
  · subst m
    have he : (schwartzSeminormFamily ℂ (ParticleConfiguration n) ℂ i).comp
        ((wickCoreSchwartzProjectionLM n).comp (DirectSum.lof ℂ ℕ (fun m => bosonicSchwartz m) n)) =
        (schwartzSeminormFamily ℂ (ParticleConfiguration n) ℂ i).comp (bosonicSchwartz n).subtype := by
      ext x
      simp [wickCoreSchwartzProjectionLM,DirectSum.lof_apply]
    rw [← Seminorm.comp_comp,he]
    exact ((schwartz_withSeminorms ℂ (ParticleConfiguration n) ℂ).continuous_seminorm i).comp continuous_subtype_val
  · have he : (wickCoreSchwartzProjectionLM n).comp (DirectSum.lof ℂ ℕ (fun k => bosonicSchwartz k) m)=0 := by
      ext x z
      change ((DirectSum.lof ℂ ℕ (fun k => bosonicSchwartz k) m x) n).val z=0
      rw [DirectSum.lof_eq_of,DirectSum.of_eq_of_ne _ _ _ (Ne.symm hm)]
      rfl
    rw [← Seminorm.comp_comp,he]
    simpa using (continuous_const : Continuous (fun _ : bosonicSchwartz m => (0:ℝ)))

def wickCoreSchwartzProjectionCLM (n : ℕ) : FiniteParticleCore →L[ℂ] 𝓢(ParticleConfiguration n,ℂ) :=
  ⟨wickCoreSchwartzProjectionLM n,wick_core_schwartz_projection_continuous n⟩

lemma wick_core_shift_seminorm_summable (r : ℕ)
    (p : ∀ n,Seminorm ℂ 𝓢(ParticleConfiguration (n+r),ℂ)) (u : FiniteParticleCore) :
    Summable (fun n => p n (u (n+r)).val) := by
  apply summable_of_ne_finset_zero (s:=Finset.range (wickCoreCutoff u))
  intro n hn
  have hz : u (n+r)=0 := wickCoreCutoff_zero u (n+r)
    ((Nat.le_of_not_lt (by simpa only [Finset.mem_range] using hn)).trans (Nat.le_add_right n r))
  simp [hz]

/-- Actual finite-support sum of shifted sector seminorms. The topology is
unchanged; continuity is proved through its original universal property. -/
def wickCoreShiftSeminorm (r : ℕ)
    (p : ∀ n,Seminorm ℂ 𝓢(ParticleConfiguration (n+r),ℂ)) : Seminorm ℂ FiniteParticleCore :=
  Seminorm.of (fun u => ∑' n,p n (u (n+r)).val)
    (by
      intro u v
      have hs := (wick_core_shift_seminorm_summable r p u).add
        (wick_core_shift_seminorm_summable r p v)
      calc
        _ ≤ ∑' n,(p n (u (n+r)).val+p n (v (n+r)).val) :=
          (wick_core_shift_seminorm_summable r p (u+v)).tsum_le_tsum
            (fun n => by simpa using map_add_le_add (p n) (u (n+r)).val (v (n+r)).val) hs
        _ = _ := ((wick_core_shift_seminorm_summable r p u).tsum_add
          (wick_core_shift_seminorm_summable r p v)))
    (by
      intro c u
      dsimp only
      calc
        _ = ∑' n,‖c‖*p n (u (n+r)).val := by
          apply tsum_congr
          intro n
          change p n (c • (u (n+r)).val)=_
          exact map_smul_eq_mul (p n) c _
        _ = _ := tsum_mul_left)

lemma wick_core_shift_seminorm_apply (r : ℕ)
    (p : ∀ n,Seminorm ℂ 𝓢(ParticleConfiguration (n+r),ℂ)) (u : FiniteParticleCore) :
    wickCoreShiftSeminorm r p u=∑' n,p n (u (n+r)).val := rfl

lemma wick_core_shift_seminorm_entry_le (r n : ℕ)
    (p : ∀ n,Seminorm ℂ 𝓢(ParticleConfiguration (n+r),ℂ)) (u : FiniteParticleCore) :
    p n (u (n+r)).val≤wickCoreShiftSeminorm r p u := by
  exact (wick_core_shift_seminorm_summable r p u).le_tsum n (fun _ _ => apply_nonneg _ _)

lemma wick_core_shift_seminorm_continuous (r : ℕ)
    (p : ∀ n,Seminorm ℂ 𝓢(ParticleConfiguration (n+r),ℂ)) (hp : ∀ n,Continuous (p n)) :
    Continuous (wickCoreShiftSeminorm r p) := by
  apply core_continuous_seminorm_of_sector_continuous
  intro m
  have he : (fun x : bosonicSchwartz m =>
      wickCoreShiftSeminorm r p (DirectSum.lof ℂ ℕ (fun k => bosonicSchwartz k) m x)) =
      (fun x => ∑ n ∈ Finset.range (m+1),p n
        ((DirectSum.lof ℂ ℕ (fun k => bosonicSchwartz k) m x) (n+r)).val) := by
    funext x
    apply tsum_eq_sum
    intro n hn
    have hne : n+r≠m := by have h := Nat.le_of_not_lt (by simpa only [Finset.mem_range] using hn);omega
    simp [DirectSum.lof_eq_of,DirectSum.of_eq_of_ne _ _ _ hne]
  change Continuous (fun x : bosonicSchwartz m =>
    wickCoreShiftSeminorm r p (DirectSum.lof ℂ ℕ (fun k => bosonicSchwartz k) m x))
  rw [he]
  apply continuous_finset_sum
  intro n hn
  exact (hp n).comp ((wickCoreSchwartzProjectionCLM (n+r)).continuous.comp
    (finiteParticleCore_lof_continuous m))


lemma wick_core_shift_seminorm_sum_le (r : ℕ)
    (p : ∀ n,Seminorm ℂ 𝓢(ParticleConfiguration (n+r),ℂ)) (u : FiniteParticleCore)
    (S : Finset ℕ) :
    (∑ n ∈ S,p n (u (n+r)).val)≤wickCoreShiftSeminorm r p u :=
  (wick_core_shift_seminorm_summable r p u).sum_le_tsum S (fun _ _ => apply_nonneg _ _)

lemma wick_core_shift_product_bound (r t : ℕ)
    (p : ∀ n,Seminorm ℂ 𝓢(ParticleConfiguration (n+r),ℂ))
    (q : ∀ n,Seminorm ℂ 𝓢(ParticleConfiguration (n+t),ℂ))
    (u v : FiniteParticleCore) (S : Finset ℕ) :
    (∑ n ∈ S,p n (u (n+r)).val*q n (v (n+t)).val)≤
      wickCoreShiftSeminorm r p u*wickCoreShiftSeminorm t q v := by
  calc
    _ ≤ ∑ n ∈ S,p n (u (n+r)).val*wickCoreShiftSeminorm t q v := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left (wick_core_shift_seminorm_entry_le t n q v) (apply_nonneg _ _)
    _ = (∑ n ∈ S,p n (u (n+r)).val)*wickCoreShiftSeminorm t q v := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (wick_core_shift_seminorm_sum_le r p u S) (apply_nonneg _ _)

end AASCKleinGordon
