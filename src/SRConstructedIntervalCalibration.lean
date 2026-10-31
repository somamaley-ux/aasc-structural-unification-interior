import Mathlib.Data.Real.Embedding
import Mathlib.Tactic

/-! SR Lemma 6.2: a real normalized duration is constructed from the original
ordered Archimedean interval group and its actual positive unit. Mathlib's
embedReal is the explicit supremum of rational comparison cuts. No real-valued
duration receipt or continuity of a candidate receipt is an existence premise.
Unique divisibility of the source's ideal branch is not needed for this stronger
ordered-group embedding statement; it remains relevant to original subdivision. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
variable {A:Type*} [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A]
  [One A] [ZeroLEOneClass A] [NeZero (1:A)] [Archimedean A]

theorem sr_normalized_original_interval_receipt_strictly_preserves_order
    (d:A →+o ℝ) (unit:d 1=1) : StrictMono d := by
  apply (strictMono_iff_map_pos d).mpr
  intro a ha
  obtain ⟨n,hn⟩:=Archimedean.arch (1:A) ha
  have hh:=d.monotone' hn
  change d 1≤d (n • a) at hh
  simp only [unit,map_nsmul,nsmul_eq_mul] at hh
  by_contra hnot
  have hp:(n:ℝ)*d a≤0:=mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (le_of_not_gt hnot)
  linarith

theorem sr_original_rational_interval_comparisons_fix_each_real_answer
    (d:A →+o ℝ) (unit:d 1=1) (a:A) (q:ℚ) :
    (q:ℝ)<d a ↔ q.num • (1:A)<q.den • a := by
  have hd:0<(q.den:ℝ):=Nat.cast_pos.mpr q.den_pos
  have hm:=sr_normalized_original_interval_receipt_strictly_preserves_order d unit
  calc
    (q:ℝ)<d a ↔ (q.num:ℝ)<(q.den:ℝ)*d a:=by
      rw [Rat.cast_def,div_lt_iff₀ hd,mul_comm]
    _ ↔ d (q.num • (1:A))<d (q.den • a):=by
      simp only [map_zsmul,map_nsmul,unit,zsmul_eq_mul,nsmul_eq_mul,mul_one]
    _ ↔ q.num • (1:A)<q.den • a:=hm.lt_iff_lt

theorem sr_same_original_interval_order_and_unit_force_same_duration
    (d e:A →+o ℝ) (du:d 1=1) (eu:e 1=1) : d=e := by
  ext a
  apply eq_of_forall_rat_lt_iff_lt
  intro q
  exact (sr_original_rational_interval_comparisons_fix_each_real_answer d du a q).trans
    (sr_original_rational_interval_comparisons_fix_each_real_answer e eu a q).symm

def srConstructedNormalizedIntervalDuration : A →+o ℝ:=Archimedean.embedReal A

theorem sr_original_archimedean_interval_group_constructs_unique_calibrated_duration :
    ∃! d:A →+o ℝ,d 1=1 ∧ Function.Injective d := by
  refine ⟨srConstructedNormalizedIntervalDuration,?_,?_⟩
  · exact ⟨Archimedean.embedReal_one,Archimedean.embedReal_injective A⟩
  · intro other ho
    exact sr_same_original_interval_order_and_unit_force_same_duration
      other srConstructedNormalizedIntervalDuration ho.1 Archimedean.embedReal_one

#print axioms sr_normalized_original_interval_receipt_strictly_preserves_order
#print axioms sr_original_rational_interval_comparisons_fix_each_real_answer
#print axioms sr_same_original_interval_order_and_unit_force_same_duration
#print axioms sr_original_archimedean_interval_group_constructs_unique_calibrated_duration
end
end AASCMetricConstruction
