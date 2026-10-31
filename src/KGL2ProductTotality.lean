import KGL2ProductMultilinear
import PiSystemBochnerUniqueness
import Mathlib.MeasureTheory.Integral.IntegrableOn

noncomputable section
set_option maxHeartbeats 2200000
open MeasureTheory Filter Set
open scoped ENNReal
namespace AASCKleinGordon

def particleBoxTest (a : Parameters) (n : ℕ) (s : Fin n → Set Momentum)
    (hs : ∀ i,MeasurableSet (s i)) (hf : ∀ i,wignerMeasure a (s i)≠∞) :
    Fin n → OneParticleHilbert a := fun i => indicatorConstLp 2 (hs i) (hf i) (1 : ℂ)

theorem particleBoxTest_product_ae (a : Parameters) (n : ℕ) (s : Fin n → Set Momentum)
    (hs : ∀ i,MeasurableSet (s i)) (hf : ∀ i,wignerMeasure a (s i)≠∞) :
    (particleL2Product a n (particleBoxTest a n s hs hf) : ParticleConfiguration n → ℂ)=ᵐ[particleMeasure a n]
      (Set.pi Set.univ s).indicator (fun _ => (1 : ℂ)) := by
  classical
  have hi:=Measure.ae_eq_pi (μ:=fun _ : Fin n => wignerMeasure a)
    (fun i => (indicatorConstLp_coeFn (p:=2) (hs:=hs i) (hμs:=hf i) (c:=(1 : ℂ))))
  filter_upwards [particleL2Product_ae a n (particleBoxTest a n s hs hf),hi] with x hx hy
  rw [hx]
  change (∏ i,particleBoxTest a n s hs hf i (x i))=_
  have he:=congrArg (fun v : Fin n → ℂ => ∏ i,v i) hy
  change (∏ i,particleBoxTest a n s hs hf i (x i))=
    ∏ i,(s i).indicator (fun _ => (1 : ℂ)) (x i) at he
  rw [he]
  by_cases h : x∈Set.pi Set.univ s
  · rw [Set.indicator_of_mem h]
    apply Finset.prod_eq_one
    intro i _
    exact Set.indicator_of_mem (h i (Set.mem_univ i)) _
  · rw [Set.indicator_of_notMem h]
    have hn : ∃ i,x i∉s i := by simpa only [Set.mem_univ_pi,not_forall] using h
    obtain ⟨i,hi⟩:=hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

theorem particleBoxTest_inner (a : Parameters) (n : ℕ) (s : Fin n → Set Momentum)
    (hs : ∀ i,MeasurableSet (s i)) (hf : ∀ i,wignerMeasure a (s i)≠∞) (v : ParticleHilbert a n) :
    inner ℂ (particleL2Product a n (particleBoxTest a n s hs hf)) v=
      ∫ x in Set.pi Set.univ s,v x ∂particleMeasure a n := by
  rw [L2.inner_def]
  have hm : MeasurableSet (Set.pi Set.univ s):=MeasurableSet.univ_pi hs
  calc
    _=∫ x,(Set.pi Set.univ s).indicator (fun x => v x) x ∂particleMeasure a n := by
      apply integral_congr_ae
      filter_upwards [particleBoxTest_product_ae a n s hs hf] with x hx
      rw [hx]
      by_cases h : x∈Set.pi Set.univ s <;> simp [h]
    _=_ := integral_indicator hm

def particleSpanningBox (a : Parameters) (n R : ℕ) : Set (ParticleConfiguration n) :=
  Set.pi Set.univ (fun _ : Fin n => spanningSets (wignerMeasure a) R)

theorem particleSpanningBox_measurable (a : Parameters) (n R : ℕ) :
    MeasurableSet (particleSpanningBox a n R) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_spanningSets _ _)

theorem particleSpanningBox_finite (a : Parameters) (n R : ℕ) :
    particleMeasure a n (particleSpanningBox a n R)≠∞ := by
  rw [particleMeasure,particleSpanningBox,Measure.pi_pi]
  exact ENNReal.prod_ne_top (fun _ _ => (measure_spanningSets_lt_top (wignerMeasure a) R).ne)

theorem particleSpanningBox_cover (a : Parameters) (n : ℕ) (x : ParticleConfiguration n) :
    ∃ R,x∈particleSpanningBox a n R := by
  classical
  have hx (i : Fin n) : ∃ R,x i∈spanningSets (wignerMeasure a) R := by
    have hm : x i∈⋃ R,spanningSets (wignerMeasure a) R := by rw [iUnion_spanningSets]; trivial
    exact Set.mem_iUnion.mp hm
  choose r hr using hx
  refine ⟨∑ i,r i,fun i _ => ?_⟩
  apply monotone_spanningSets (wignerMeasure a) ?_ (hr i)
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (r j)) (Finset.mem_univ i)

/-- Products are total in the original product-Wigner L2 space. The proof uses
finite measured rectangles and native complex Bochner uniqueness. -/
theorem particleL2Product_total (a : Parameters) (n : ℕ) (v : ParticleHilbert a n)
    (h : ∀ f : Fin n → OneParticleHilbert a,inner ℂ (particleL2Product a n f) v=0) : v=0 := by
  have hb (s : Fin n → Set Momentum) (hs : ∀ i,MeasurableSet (s i))
      (hf : ∀ i,wignerMeasure a (s i)≠∞) : ∫ x in Set.pi Set.univ s,v x ∂particleMeasure a n=0 := by
    rw [← particleBoxTest_inner a n s hs hf v]
    exact h _
  have hR (R : ℕ) : (v : ParticleConfiguration n → ℂ)=ᵐ[(particleMeasure a n).restrict (particleSpanningBox a n R)] 0 := by
    have hi:=integrableOn_Lp_of_measure_ne_top v (by norm_num : 1≤(2 : ℝ≥0∞))
      (particleSpanningBox_finite a n R)
    change Integrable (v : ParticleConfiguration n → ℂ)
      ((Measure.pi (fun _ : Fin n => wignerMeasure a)).restrict
        (Set.pi Set.univ (fun _ : Fin n => spanningSets (wignerMeasure a) R))) at hi
    rw [Measure.restrict_pi_pi] at hi
    change (v : ParticleConfiguration n → ℂ)=ᵐ[
      (Measure.pi (fun _ : Fin n => wignerMeasure a)).restrict
        (Set.pi Set.univ (fun _ : Fin n => spanningSets (wignerMeasure a) R))] 0
    rw [Measure.restrict_pi_pi]
    apply integrable_zero_of_all_box_integrals _ _ hi
    intro s hs
    have hbox : MeasurableSet (Set.pi Set.univ s):=MeasurableSet.univ_pi hs
    rw [← Measure.restrict_pi_pi,Measure.restrict_restrict hbox,← Set.pi_inter_distrib]
    exact hb (fun i => s i∩spanningSets (wignerMeasure a) R)
      (fun i => (hs i).inter (measurableSet_spanningSets _ _))
      (fun i => ne_top_of_le_ne_top (measure_spanningSets_lt_top (wignerMeasure a) R).ne
        (measure_mono Set.inter_subset_right))
  have hz : (v : ParticleConfiguration n → ℂ)=ᵐ[particleMeasure a n] 0 := by
    have he (R : ℕ) : ∀ᵐ x ∂particleMeasure a n,x∈particleSpanningBox a n R → v x=0 :=
      (ae_restrict_iff' (particleSpanningBox_measurable a n R)).mp (hR R)
    filter_upwards [ae_all_iff.mpr he] with x hx
    obtain ⟨R,hxR⟩:=particleSpanningBox_cover a n x
    exact hx R hxR
  apply Lp.ext
  have hzero : (0 : ParticleHilbert a n)=ᵐ[particleMeasure a n] (fun _ => (0 : ℂ)):=Lp.coeFn_zero _ _ _
  exact hz.trans hzero.symm

end AASCKleinGordon
