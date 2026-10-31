import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Mul

/-! CSP-C Lemma 8.1, PDF p.27: an explicit finite inverse, not an inverse
certificate stored in a structure. The algebra is allowed to be noncommutative,
so this applies to matrices over a finite coefficient algebra. Nilpotence of the
positive-degree matrix is a separate exterior-degree theorem. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
open scoped BigOperators

variable {A : Type*} [Ring A]

def nativeFiniteNeumannSum (q : A) (n : ℕ) : A :=
  ∑ i ∈ Finset.range n, (-q)^i

theorem native_finite_neumann_left (q : A) (n : ℕ) (nilpotent : q^n=0) :
    (1+q)*nativeFiniteNeumannSum q n=1 := by
  have hz : (-q)^n=0 := by rw [neg_pow,nilpotent,mul_zero]
  simpa only [nativeFiniteNeumannSum,sub_neg_eq_add,hz,sub_zero] using
    mul_neg_geom_sum (-q) n

theorem native_finite_neumann_right (q : A) (n : ℕ) (nilpotent : q^n=0) :
    nativeFiniteNeumannSum q n*(1+q)=1 := by
  have hz : (-q)^n=0 := by rw [neg_pow,nilpotent,mul_zero]
  simpa only [nativeFiniteNeumannSum,sub_neg_eq_add,hz,sub_zero] using
    geom_sum_mul_neg (-q) n

def nativeNilpotentPerturbationInverse (bodyInverse perturbation : A) (n : ℕ) : A :=
  nativeFiniteNeumannSum (bodyInverse*perturbation) n*bodyInverse

theorem native_nilpotent_perturbation_inverse_right (body bodyInverse perturbation : A)
    (n : ℕ) (rightBody : body*bodyInverse=1) (leftBody : bodyInverse*body=1)
    (nilpotent : (bodyInverse*perturbation)^n=0) :
    nativeNilpotentPerturbationInverse bodyInverse perturbation n*(body+perturbation)=1 := by
  unfold nativeNilpotentPerturbationInverse
  rw [mul_assoc,mul_add,leftBody]
  exact native_finite_neumann_right _ n nilpotent

theorem native_nilpotent_perturbation_inverse_left (body bodyInverse perturbation : A)
    (n : ℕ) (rightBody : body*bodyInverse=1) (leftBody : bodyInverse*body=1)
    (nilpotent : (bodyInverse*perturbation)^n=0) :
    (body+perturbation)*nativeNilpotentPerturbationInverse bodyInverse perturbation n=1 := by
  have factor : body+perturbation=body*(1+bodyInverse*perturbation) := by
    rw [mul_add,mul_one,← mul_assoc,rightBody,one_mul]
  unfold nativeNilpotentPerturbationInverse
  rw [factor,mul_assoc,← mul_assoc (1+bodyInverse*perturbation),
    native_finite_neumann_left _ n nilpotent,one_mul,rightBody]

theorem native_nilpotent_perturbation_inverse_unique (body bodyInverse perturbation : A)
    (n : ℕ) (rightBody : body*bodyInverse=1) (leftBody : bodyInverse*body=1)
    (nilpotent : (bodyInverse*perturbation)^n=0) (candidate : A)
    (rightCandidate : (body+perturbation)*candidate=1) :
    candidate=nativeNilpotentPerturbationInverse bodyInverse perturbation n := by
  calc
    candidate=1*candidate := (one_mul _).symm
    _=(nativeNilpotentPerturbationInverse bodyInverse perturbation n*(body+perturbation))*candidate := by
      rw [native_nilpotent_perturbation_inverse_right body bodyInverse perturbation n rightBody leftBody nilpotent]
    _=nativeNilpotentPerturbationInverse bodyInverse perturbation n := by rw [mul_assoc,rightCandidate,mul_one]

theorem native_square_zero_inverse_first_correction (bodyInverse perturbation : A) :
    nativeNilpotentPerturbationInverse bodyInverse perturbation 2=
      bodyInverse-bodyInverse*perturbation*bodyInverse := by
  simp [nativeNilpotentPerturbationInverse,nativeFiniteNeumannSum,Finset.sum_range_succ]
  noncomm_ring

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem native_exterior_pair_square_zero (u v : M) :
    (ExteriorAlgebra.ι R u*ExteriorAlgebra.ι R v)^2=0 := by
  let x:=ExteriorAlgebra.ι R u
  let y:=ExteriorAlgebra.ι R v
  have hs : y*x=-(x*y) := by
    apply eq_neg_of_add_eq_zero_left
    exact ExteriorAlgebra.ι_add_mul_swap v u
  calc
    (x*y)^2=x*(y*x)*y := by noncomm_ring
    _=-(x*x)*(y*y) := by rw [hs]; noncomm_ring
    _=0 := by change -(ExteriorAlgebra.ι R u*ExteriorAlgebra.ι R u)*(ExteriorAlgebra.ι R v*ExteriorAlgebra.ι R v)=0
              rw [ExteriorAlgebra.ι_sq_zero]; simp

def nativeCSPDegreeTwoCoefficient (N : ℕ) (i j : Fin N) :
    ExteriorAlgebra ℂ (Fin N → ℂ) :=
  Complex.I • (ExteriorAlgebra.ι ℂ (Pi.single i 1)*ExteriorAlgebra.ι ℂ (Pi.single j 1))

theorem native_csp_degree_two_coefficient_square_zero (N : ℕ) (i j : Fin N) :
    (nativeCSPDegreeTwoCoefficient N i j)^2=0 := by
  unfold nativeCSPDegreeTwoCoefficient
  have hz := native_exterior_pair_square_zero (R := ℂ) (M := Fin N → ℂ) (Pi.single i 1) (Pi.single j 1)
  rw [pow_two] at hz
  rw [pow_two,smul_mul_smul,hz,smul_zero]

#print axioms native_finite_neumann_left
#print axioms native_finite_neumann_right
#print axioms native_nilpotent_perturbation_inverse_right
#print axioms native_nilpotent_perturbation_inverse_left
#print axioms native_nilpotent_perturbation_inverse_unique
#print axioms native_square_zero_inverse_first_correction
#print axioms native_exterior_pair_square_zero
#print axioms native_csp_degree_two_coefficient_square_zero
end
end AASCSemanticExhaustion
