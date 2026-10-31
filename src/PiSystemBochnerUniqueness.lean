import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set
namespace AASCKleinGordon

/-- Complex Bochner uniqueness on actual finite-product boxes. No signed-measure
certificate or product-density premise is required. -/
theorem integrable_zero_of_all_box_integrals {n : ℕ} {X : Fin n → Type*}
    [∀ i,MeasurableSpace (X i)] (μ : ∀ i,Measure (X i))
    (f : (∀ i,X i) → ℂ) (hf : Integrable f (Measure.pi μ))
    (boxes : ∀ (s : ∀ i,Set (X i)),(∀ i,MeasurableSet (s i)) →
      ∫ x in Set.pi Set.univ s,f x ∂Measure.pi μ=0) : f=ᵐ[Measure.pi μ] 0 := by
  have ht : ∫ x,f x ∂Measure.pi μ=0 := by
    simpa only [Set.pi_univ,Measure.restrict_univ] using boxes (fun _ => Set.univ) (fun _ => MeasurableSet.univ)
  have hs : ∀ s,MeasurableSet s → ∫ x in s,f x ∂Measure.pi μ=0 := by
    apply MeasurableSpace.induction_on_inter (C:=fun s _ => ∫ x in s,f x ∂Measure.pi μ=0)
      (h_eq:=generateFrom_pi.symm) (h_inter:=isPiSystem_pi)
    · simp
    · rintro _ ⟨s,hs,rfl⟩
      exact boxes s (fun i => hs i (Set.mem_univ i))
    · intro s hs hzero
      rw [setIntegral_compl hs hf,ht,hzero,sub_self]
    · intro s hd hm hzero
      rw [integral_iUnion hm hd hf.integrableOn]
      simp only [hzero,tsum_zero]
  exact hf.ae_eq_zero_of_forall_setIntegral_eq_zero (fun s h _ => hs s h)

end AASCKleinGordon
