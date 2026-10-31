import NativeExteriorMetricFirstCorrection
import Mathlib.Algebra.DualNumber

/-! Exact coefficient expansion of covariant divergence, CSP-C 9.3 p.32.
This is an algebraic first-jet calculation; no Ward/conservation result is
assumed. It retains inverse-metric and both connection-stress cross terms. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open scoped BigOperators

abbrev NativeTwoTensor (R : Type*) := Fin 4 → Fin 4 → R
abbrev NativeConnectionJet (R : Type*) := Fin 4 → Fin 4 → Fin 4 → R

def nativeCovariantStressJet {R : Type*} [Ring R] (Γ : NativeConnectionJet R) (T : NativeTwoTensor R)
    (D : NativeConnectionJet R) (a b c : Fin 4) : R :=
  D a b c-∑ d, (Γ d a b*T d c+Γ d a c*T b d)

def nativeStressDivergenceJet {R : Type*} [Ring R] (B : NativeTwoTensor R) (Γ : NativeConnectionJet R)
    (T : NativeTwoTensor R) (D : NativeConnectionJet R) (ν : Fin 4) : R :=
  ∑ a, ∑ b, B a b*nativeCovariantStressJet Γ T D a b ν

variable {R : Type*} [CommRing R]

theorem native_covariant_stress_jet_body (Γ : NativeConnectionJet (DualNumber R))
    (T : NativeTwoTensor (DualNumber R)) (D : NativeConnectionJet (DualNumber R))
    (a b c : Fin 4) :
    (nativeCovariantStressJet Γ T D a b c).fst=
      nativeCovariantStressJet (fun d a b => (Γ d a b).fst)
        (fun a b => (T a b).fst) (fun a b c => (D a b c).fst) a b c := by
  simp [nativeCovariantStressJet,TrivSqZeroExt.fst_sum]

theorem native_covariant_stress_jet_first_coefficient (Γ : NativeConnectionJet (DualNumber R))
    (T : NativeTwoTensor (DualNumber R)) (D : NativeConnectionJet (DualNumber R))
    (a b c : Fin 4) :
    (nativeCovariantStressJet Γ T D a b c).snd=
      nativeCovariantStressJet (fun d a b => (Γ d a b).fst)
        (fun a b => (T a b).snd) (fun a b c => (D a b c).snd) a b c-
      ∑ d, ((Γ d a b).snd*(T d c).fst+(Γ d a c).snd*(T b d).fst) := by
  simp only [nativeCovariantStressJet,TrivSqZeroExt.snd_sub,TrivSqZeroExt.snd_sum,
    TrivSqZeroExt.snd_add,DualNumber.snd_mul]
  simp only [Finset.sum_add_distrib]
  ring

theorem native_stress_divergence_first_coefficient (B : NativeTwoTensor (DualNumber R))
    (Γ : NativeConnectionJet (DualNumber R)) (T : NativeTwoTensor (DualNumber R))
    (D : NativeConnectionJet (DualNumber R)) (ν : Fin 4) :
    (nativeStressDivergenceJet B Γ T D ν).snd=
      nativeStressDivergenceJet (fun a b => (B a b).fst) (fun d a b => (Γ d a b).fst)
        (fun a b => (T a b).snd) (fun a b c => (D a b c).snd) ν+
      (∑ a, ∑ b, (B a b).snd*nativeCovariantStressJet (fun d a b => (Γ d a b).fst)
        (fun a b => (T a b).fst) (fun a b c => (D a b c).fst) a b ν)-
      ∑ a, ∑ b, (B a b).fst*
        ∑ d, ((Γ d a b).snd*(T d ν).fst+(Γ d a ν).snd*(T b d).fst) := by
  simp only [nativeStressDivergenceJet,TrivSqZeroExt.snd_sum,DualNumber.snd_mul,
    native_covariant_stress_jet_first_coefficient,native_covariant_stress_jet_body,mul_sub]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  ring

/-- Scalar evaluation into an actual square-zero subalgebra; used with the
actual i θ_i θ_j coefficient of CSP-C, whose square-zero law is already proved. -/
def nativeSquareZeroEvaluation {A : Type*} [Ring A] [Algebra R A]
    (ε : A) (hε : ε*ε=0) : DualNumber R →ₐ[R] A :=
  TrivSqZeroExt.liftEquivOfComm ⟨
    { toFun:=fun r => algebraMap R A r*ε
      map_add':=by intro r s; simp [map_add,add_mul]
      map_smul':=by intro r s; simp [Algebra.smul_def,map_mul,mul_assoc] },
    fun r s => native_coefficient_entry_product_zero ε hε r s⟩

theorem native_square_zero_evaluation_components {A : Type*} [Ring A] [Algebra R A]
    (ε : A) (hε : ε*ε=0) (x : DualNumber R) :
    nativeSquareZeroEvaluation ε hε x=algebraMap R A x.fst+algebraMap R A x.snd*ε := rfl

theorem native_covariant_stress_jet_evaluation {A : Type*} [Ring A] [Algebra R A]
    (ε : A) (hε : ε*ε=0) (Γ : NativeConnectionJet (DualNumber R))
    (T : NativeTwoTensor (DualNumber R)) (D : NativeConnectionJet (DualNumber R))
    (a b c : Fin 4) :
    nativeSquareZeroEvaluation ε hε (nativeCovariantStressJet Γ T D a b c)=
      (nativeSquareZeroEvaluation ε hε (D a b c))-
        ∑ d, (nativeSquareZeroEvaluation ε hε (Γ d a b)*nativeSquareZeroEvaluation ε hε (T d c)+
          nativeSquareZeroEvaluation ε hε (Γ d a c)*nativeSquareZeroEvaluation ε hε (T b d)) := by
  simp only [nativeCovariantStressJet,map_sub,map_sum,map_add,map_mul]

theorem native_stress_divergence_jet_evaluation {A : Type*} [Ring A] [Algebra R A]
    (ε : A) (hε : ε*ε=0) (B : NativeTwoTensor (DualNumber R))
    (Γ : NativeConnectionJet (DualNumber R)) (T : NativeTwoTensor (DualNumber R))
    (D : NativeConnectionJet (DualNumber R)) (ν : Fin 4) :
    nativeSquareZeroEvaluation ε hε (nativeStressDivergenceJet B Γ T D ν)=
      nativeStressDivergenceJet (fun a b => nativeSquareZeroEvaluation ε hε (B a b))
        (fun a b c => nativeSquareZeroEvaluation ε hε (Γ a b c))
        (fun a b => nativeSquareZeroEvaluation ε hε (T a b))
        (fun a b c => nativeSquareZeroEvaluation ε hε (D a b c)) ν := by
  simp only [nativeStressDivergenceJet,nativeCovariantStressJet,map_sum,map_mul,map_sub,map_add]

#print axioms native_covariant_stress_jet_body
#print axioms native_covariant_stress_jet_first_coefficient
#print axioms native_stress_divergence_first_coefficient
#print axioms native_square_zero_evaluation_components
#print axioms native_covariant_stress_jet_evaluation
#print axioms native_stress_divergence_jet_evaluation
end
end AASCSemanticExhaustion
