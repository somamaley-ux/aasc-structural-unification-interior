import KGFockContractiveSymbols

noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
open scoped Topology
namespace AASCKleinGordon

theorem symbolSector_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (a : Parameters) (S : ι → FockContractiveSymbol a)
    (T : FockContractiveSymbol a)
    (hl : ∀ n,∀ᵐ x ∂particleMeasure a n,Tendsto (fun k => (S k).value n x) l (𝓝 (T.value n x)))
    (n : ℕ) (f : bosonicHilbertSector a n) :
    Tendsto (fun k => symbolSector a (S k) n f) l (𝓝 (symbolSector a T n f)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun k => (symbolSector a (S k) n f).val-(symbolSector a T n f).val) l (𝓝 0)
  apply Multiplication.L2_tendsto_zero_of_dominated _
    (fun k x => ((S k).value n x-T.value n x)*f.val x) ?_ ?_
    (fun x => 2*‖f.val x‖) ((Lp.memLp f.val).norm.const_mul 2) ?_ ?_
  · intro k
    filter_upwards [Lp.coeFn_sub (symbolSector a (S k) n f).val (symbolSector a T n f).val,
      symbolSector_ae a (S k) n f,symbolSector_ae a T n f] with x hx hy hz
    simp only [Pi.sub_apply] at hx
    rw [hx,hy,hz,sub_mul]
  · intro k
    exact (((S k).measurable n).aestronglyMeasurable.sub
      (T.measurable n).aestronglyMeasurable).mul (Lp.memLp f.val).1
  · exact Eventually.of_forall (fun k => Eventually.of_forall (fun x => by
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have h:=(norm_sub_le ((S k).value n x) (T.value n x))
      linarith [(S k).bound n x,T.bound n x]))
  · exact (hl n).mono (fun x hx => by
      simpa only [sub_self,zero_mul] using (hx.sub_const (T.value n x)).mul_const (f.val x))

theorem symbolOperator_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (a : Parameters) (S : ι → FockContractiveSymbol a)
    (T : FockContractiveSymbol a)
    (hl : ∀ n,∀ᵐ x ∂particleMeasure a n,Tendsto (fun k => (S k).value n x) l (𝓝 (T.value n x)))
    (f : FockHilbert a) :
    Tendsto (fun k => symbolOperator a (S k) f) l (𝓝 (symbolOperator a T f)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  apply HilbertSum.tendsto_zero_of_dominated _ (fun n => 2*‖f n‖) ?_ ?_ ?_
  · have hh:=((lp.memℓp f).summable (by norm_num)).mul_left 4
    convert hh using 1
    funext n
    simp only [ENNReal.toReal_ofNat,Real.rpow_two,mul_pow]
    ring
  · intro n
    have hh:=(symbolSector_tendsto a S T hl n (f n)).sub_const (symbolSector a T n (f n))
    simpa only [sub_self] using hh
  · exact Eventually.of_forall (fun k n => by
      change ‖symbolSector a (S k) n (f n)-symbolSector a T n (f n)‖≤2*‖f n‖
      have hh:=norm_sub_le (symbolSector a (S k) n (f n)) (symbolSector a T n (f n))
      linarith [symbolSector_contraction a (S k) n (f n),symbolSector_contraction a T n (f n)])

end AASCKleinGordon
