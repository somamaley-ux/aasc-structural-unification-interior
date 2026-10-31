import KGFockTranslationContinuity
import KGBosonicMultiplicationInvariance

noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
namespace AASCKleinGordon

/-- Actual measurable permutation-invariant bounded coefficients, not a spectral certificate. -/
structure FockContractiveSymbol (a : Parameters) where
  value : ∀ n,ParticleConfiguration n → ℂ
  measurable : ∀ n,Measurable (value n)
  invariant : ∀ n (σ : Equiv.Perm (Fin n)) x,value n (particlePermutation n σ x)=value n x
  bound : ∀ n x,‖value n x‖≤1

def symbolSector (a : Parameters) (S : FockContractiveSymbol a) (n : ℕ) :
    bosonicHilbertSector a n →L[ℂ] bosonicHilbertSector a n :=
  ((Multiplication.boundedMul (S.value n) (S.measurable n).aestronglyMeasurable 1
    (Eventually.of_forall (S.bound n))).comp (bosonicHilbertSector a n).subtypeL).codRestrict
      (bosonicHilbertSector a n) (fun f => bosonic_multiplication_output_fixed a n _
        (S.invariant n) f _ (Multiplication.boundedMul_ae (S.value n) (S.measurable n).aestronglyMeasurable 1
          (Eventually.of_forall (S.bound n)) f.val))

theorem symbolSector_ae (a : Parameters) (S : FockContractiveSymbol a) (n : ℕ)
    (f : bosonicHilbertSector a n) :
    (symbolSector a S n f).val=ᵐ[particleMeasure a n] (fun x => S.value n x*f.val x) :=
  Multiplication.boundedMul_ae (S.value n) (S.measurable n).aestronglyMeasurable 1
    (Eventually.of_forall (S.bound n)) f.val

theorem symbolSector_contraction (a : Parameters) (S : FockContractiveSymbol a) (n : ℕ)
    (f : bosonicHilbertSector a n) : ‖symbolSector a S n f‖≤‖f‖ := by
  change ‖Multiplication.boundedMulLinear (S.value n) (S.measurable n).aestronglyMeasurable 1
    (Eventually.of_forall (S.bound n)) f.val‖≤‖f.val‖
  simpa only [one_mul] using Multiplication.boundedMulLinear_norm_le (S.value n) (S.measurable n).aestronglyMeasurable 1
    (Eventually.of_forall (S.bound n)) f.val

def symbolOperator (a : Parameters) (S : FockContractiveSymbol a) :
    FockHilbert a →L[ℂ] FockHilbert a :=
  HilbertSum.diagonal (symbolSector a S) (symbolSector_contraction a S)

theorem symbolOperator_ae (a : Parameters) (S : FockContractiveSymbol a) (f : FockHilbert a) (n : ℕ) :
    (symbolOperator a S f n).val=ᵐ[particleMeasure a n] (fun x => S.value n x*(f n).val x) :=
  symbolSector_ae a S n (f n)

theorem symbolOperator_eq_of_value_eq (a : Parameters) (S T : FockContractiveSymbol a)
    (h : ∀ n x,S.value n x=T.value n x) : symbolOperator a S=symbolOperator a T := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext n
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [symbolOperator_ae a S f n,symbolOperator_ae a T f n] with x hx hy
  rw [hx,hy,h]

def symbolProduct (a : Parameters) (S T : FockContractiveSymbol a) : FockContractiveSymbol a where
  value n x:=S.value n x*T.value n x
  measurable n:=(S.measurable n).mul (T.measurable n)
  invariant n σ x:=by rw [S.invariant,T.invariant]
  bound n x:=by
    rw [norm_mul]
    calc
      _ ≤ 1*1 := mul_le_mul (S.bound n x) (T.bound n x) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num

theorem symbolOperator_product (a : Parameters) (S T : FockContractiveSymbol a) :
    (symbolOperator a S).comp (symbolOperator a T)=symbolOperator a (symbolProduct a S T) := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext n
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [symbolOperator_ae a S (symbolOperator a T f) n,
    symbolOperator_ae a T f n,symbolOperator_ae a (symbolProduct a S T) f n] with x hx hy hz
  change (symbolOperator a S (symbolOperator a T f) n).val x=_
  rw [hx,hy,hz]
  exact (mul_assoc _ _ _).symm

theorem symbolOperator_symmetric (a : Parameters) (S : FockContractiveSymbol a)
    (hr : ∀ n x,star (S.value n x)=S.value n x) (f g : FockHilbert a) :
    inner ℂ (symbolOperator a S f) g=inner ℂ f (symbolOperator a S g) := by
  apply HilbertSum.diagonal_symmetric
  intro n u v
  exact Multiplication.boundedMul_symmetric (S.value n) (S.measurable n).aestronglyMeasurable 1
    (Eventually.of_forall (S.bound n)) (Eventually.of_forall (hr n)) u.val v.val

end AASCKleinGordon
