import KGNativeWickRayOperationalSource
import KGNativeWickQuadraticExtension

noncomputable section
set_option maxHeartbeats 8000000
open scoped SchwartzMap NNReal
open AASCKleinGordon.SchwartzOperations
namespace AASCKleinGordon

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma wick_finset_sup_seminorm_continuous {V ι : Type*}
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (s : Finset ι) (p : ι → Seminorm ℂ V) (hp : ∀ i ∈ s, Continuous (p i)) :
    Continuous ((s.sup p : Seminorm ℂ V) : V → ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (continuous_const : Continuous (fun _ : V => (0:ℝ)))
  | @insert i s hi ih =>
    rw [Finset.sup_insert]
    change Continuous (fun x => max (p i x) (s.sup p x))
    exact (hp i (Finset.mem_insert_self _ _)).max
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

@[simp] lemma wick_seminorm_sum_apply {V ι : Type*} [AddCommGroup V] [Module ℂ V]
    (s : Finset ι) (p : ι → Seminorm ℂ V) (x : V) :
    (∑ i ∈ s,p i) x=∑ i ∈ s,p i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi,Seminorm.add_apply,ih]

def wickSchwartzBoundSeminorm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : ℕ × ℕ) : Seminorm ℂ 𝓢(E,ℂ) :=
  (2 : ℝ≥0)^i.1 • (Finset.Iic i).sup (schwartzSeminormFamily ℂ E ℂ)

lemma wick_schwartz_bound_seminorm_apply (i : ℕ × ℕ) (f : 𝓢(E,ℂ)) :
    wickSchwartzBoundSeminorm E i f=schwartzBound i.1 i.2 f := by
  simp [wickSchwartzBoundSeminorm,schwartzBound,Seminorm.smul_apply,NNReal.smul_def]

lemma wick_schwartz_bound_seminorm_continuous (i : ℕ × ℕ) :
    Continuous (wickSchwartzBoundSeminorm E i) := by
  exact (wick_finset_sup_seminorm_continuous (Finset.Iic i) _
    (fun j _ => (schwartz_withSeminorms ℂ E ℂ).continuous_seminorm j)).const_smul _

def wickTensorBoundCoefficient (i : ℕ × ℕ) : ℝ≥0 :=
  ⟨‖realComplexMultiplication‖ * (∑ j ∈ Finset.range (i.2+1),(i.2.choose j : ℝ)), by positivity⟩

/-- Every continuous seminorm after the ACTUAL tensor map has two continuous
Schwartz seminorm controls. No tensor continuity or bound is received. -/
theorem wick_tensor_continuous_seminorm_bound
    (q : Seminorm ℂ 𝓢(E × F,ℂ)) (hq : Continuous q) :
    ∃ p₁ : Seminorm ℂ 𝓢(E,ℂ), ∃ p₂ : Seminorm ℂ 𝓢(F,ℂ),
      Continuous p₁ ∧ Continuous p₂ ∧
        ∀ f g, q (tensorLeftCLM f g)≤p₁ f*p₂ g := by
  classical
  obtain ⟨S,C,hC,hbound⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℂ (E × F) ℂ) q hq
  let p₁ : Seminorm ℂ 𝓢(E,ℂ) := C • ∑ i ∈ S,wickTensorBoundCoefficient i • wickSchwartzBoundSeminorm E i
  let p₂ : Seminorm ℂ 𝓢(F,ℂ) := ∑ i ∈ S,wickSchwartzBoundSeminorm F i
  refine ⟨p₁,p₂,?_,?_,?_⟩
  · change Continuous (fun f => p₁ f)
    simpa only [p₁,wick_seminorm_sum_apply,Seminorm.smul_apply,NNReal.smul_def,smul_eq_mul] using
      (continuous_finset_sum S (fun i _ =>
        (wick_schwartz_bound_seminorm_continuous (E:=E) i).const_smul (wickTensorBoundCoefficient i : ℝ))).const_smul (C:ℝ)
  · change Continuous (fun g => p₂ g)
    simpa only [p₂,wick_seminorm_sum_apply] using
      continuous_finset_sum S (fun i _ => wick_schwartz_bound_seminorm_continuous (E:=F) i)
  · intro f g
    have hsup : (S.sup (schwartzSeminormFamily ℂ (E × F) ℂ)) (tensorLeftCLM f g) ≤
        (∑ i ∈ S,(wickTensorBoundCoefficient i : ℝ)*wickSchwartzBoundSeminorm E i f)*p₂ g := by
      apply Seminorm.finset_sup_apply_le (mul_nonneg (Finset.sum_nonneg
        (fun i _ => mul_nonneg (wickTensorBoundCoefficient i).coe_nonneg (apply_nonneg _ _))) (apply_nonneg _ _))
      intro i hi
      have ht := tensor_seminorm_bound f g i.1 i.2
      change _≤(wickTensorBoundCoefficient i : ℝ)*schwartzBound i.1 i.2 f*schwartzBound i.1 i.2 g at ht
      rw [← wick_schwartz_bound_seminorm_apply,← wick_schwartz_bound_seminorm_apply] at ht
      have he : (wickTensorBoundCoefficient i : ℝ)*wickSchwartzBoundSeminorm E i f ≤
          ∑ j ∈ S,(wickTensorBoundCoefficient j : ℝ)*wickSchwartzBoundSeminorm E j f :=
        Finset.single_le_sum (fun j _ => mul_nonneg (wickTensorBoundCoefficient j).coe_nonneg (apply_nonneg _ _)) hi
      have hf : wickSchwartzBoundSeminorm F i g≤p₂ g := by
        change _≤(∑ j ∈ S,wickSchwartzBoundSeminorm F j) g
        simpa only [wick_seminorm_sum_apply] using
          (Finset.single_le_sum (fun j _ => apply_nonneg (wickSchwartzBoundSeminorm F j) g) hi)
      exact ht.trans (mul_le_mul he hf (apply_nonneg _ _) (Finset.sum_nonneg
        (fun j _ => mul_nonneg (wickTensorBoundCoefficient j).coe_nonneg (apply_nonneg _ _))))
    have hb := hbound (tensorLeftCLM f g)
    change q (tensorLeftCLM f g)≤(C:ℝ)*(S.sup (schwartzSeminormFamily ℂ (E × F) ℂ)) (tensorLeftCLM f g) at hb
    apply (hb.trans (mul_le_mul_of_nonneg_left hsup C.coe_nonneg)).trans_eq
    simp only [p₁,Seminorm.smul_apply,wick_seminorm_sum_apply,NNReal.smul_def,smul_eq_mul]
    ring

end AASCKleinGordon
