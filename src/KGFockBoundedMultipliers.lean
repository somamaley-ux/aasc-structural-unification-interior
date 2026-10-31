import KGBosonicMaximalMultiplication
import L2HilbertSumDiagonal

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
namespace AASCKleinGordon

variable (a : Parameters) (v : ∀ n,ParticleConfiguration n → ℝ)
variable (hv : ∀ n,Measurable (v n))
variable (hi : ∀ n (σ : Equiv.Perm (Fin n)) x,v n (particlePermutation n σ x)=v n x)

def sectorCoefficientA (n : ℕ) : bosonicHilbertSector a n →L[ℂ] bosonicHilbertSector a n :=
  Multiplication.subspaceBoundedA (v n) (hv n) (bosonicHilbertSector a n)
    (particleGraphBoundedA_preserves_bosonic a n (v n) (hv n) (hi n))

def sectorCoefficientB (n : ℕ) : bosonicHilbertSector a n →L[ℂ] bosonicHilbertSector a n :=
  Multiplication.subspaceBoundedB (v n) (hv n) (bosonicHilbertSector a n)
    (particleGraphBoundedB_preserves_bosonic a n (v n) (hv n) (hi n))

theorem sectorCoefficientA_contraction (n : ℕ) (f : bosonicHilbertSector a n) :
    ‖sectorCoefficientA a v hv hi n f‖≤‖f‖ := by
  change ‖Multiplication.graphBoundedA (v n) (hv n) f.val‖≤‖f.val‖
  simpa only [one_mul] using Multiplication.boundedMulLinear_norm_le _
    (Multiplication.graphCoefficientA_measurable (v n) (hv n)).aestronglyMeasurable 1
    (Eventually.of_forall (fun x => Multiplication.graphCoefficientA_bound (v n x))) f.val

theorem sectorCoefficientB_contraction (n : ℕ) (f : bosonicHilbertSector a n) :
    ‖sectorCoefficientB a v hv hi n f‖≤‖f‖ := by
  change ‖Multiplication.graphBoundedB (v n) (hv n) f.val‖≤‖f.val‖
  simpa only [one_mul] using Multiplication.boundedMulLinear_norm_le _
    (Multiplication.graphCoefficientB_measurable (v n) (hv n)).aestronglyMeasurable 1
    (Eventually.of_forall (fun x => Multiplication.graphCoefficientB_bound (v n x))) f.val

def fockCoefficientA : FockHilbert a →L[ℂ] FockHilbert a :=
  HilbertSum.diagonal (sectorCoefficientA a v hv hi) (sectorCoefficientA_contraction a v hv hi)

def fockCoefficientB : FockHilbert a →L[ℂ] FockHilbert a :=
  HilbertSum.diagonal (sectorCoefficientB a v hv hi) (sectorCoefficientB_contraction a v hv hi)

theorem fockCoefficientB_injective : Function.Injective (fockCoefficientB a v hv hi) :=
  HilbertSum.diagonal_injective _ _ (fun n => Multiplication.subspaceBoundedB_injective _ _ _ _)

theorem fockCoefficientA_symmetric (f g : FockHilbert a) :
    inner ℂ (fockCoefficientA a v hv hi f) g=inner ℂ f (fockCoefficientA a v hv hi g) :=
  HilbertSum.diagonal_symmetric _ _ (fun n => Multiplication.subspaceBoundedA_symmetric _ _ _ _) f g

theorem fockCoefficientB_symmetric (f g : FockHilbert a) :
    inner ℂ (fockCoefficientB a v hv hi f) g=inner ℂ f (fockCoefficientB a v hv hi g) :=
  HilbertSum.diagonal_symmetric _ _ (fun n => Multiplication.subspaceBoundedB_symmetric _ _ _ _) f g

theorem fockCoefficients_commute :
    (fockCoefficientB a v hv hi).comp (fockCoefficientA a v hv hi)=
      (fockCoefficientA a v hv hi).comp (fockCoefficientB a v hv hi) := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext n
  exact congrArg (fun C : bosonicHilbertSector a n →L[ℂ] bosonicHilbertSector a n => C (f n))
    (Multiplication.subspaceBounded_commute _ _ _ _ _)

theorem fockCoefficients_normalized :
    (fockCoefficientA a v hv hi).comp (fockCoefficientA a v hv hi)+
      (fockCoefficientB a v hv hi).comp (fockCoefficientB a v hv hi)=
        ContinuousLinearMap.id ℂ (FockHilbert a) := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext n
  exact congrArg (fun C : bosonicHilbertSector a n →L[ℂ] bosonicHilbertSector a n => C (f n))
    (Multiplication.subspaceBounded_normalized _ _ _ _ _)

end AASCKleinGordon
