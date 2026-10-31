import SKGSameMetricRegularity
import SKGScalarStressDerivative

/-! Regular scalar Legendre transform of the very same inherited density.
The evolution coordinate here is x0=c*t. No coupled or gauge Legendre map. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

def scalarCanonicalLagrangian (l mu2 phi v : ℝ) (P : Fin 3 → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (l * (v ^ 2 - ∑ i : Fin 3, P i ^ 2) - mu2 * l ^ 2 * phi ^ 2)

def scalarCanonicalMomentum (l v : ℝ) : ℝ := l * v

def scalarCanonicalVelocity (l pi : ℝ) : ℝ := pi / l

def scalarCanonicalHamiltonian (l mu2 phi pi : ℝ) (P : Fin 3 → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (pi ^ 2 / l + l * (∑ i : Fin 3, P i ^ 2) + mu2 * l ^ 2 * phi ^ 2)

theorem same_density_scalar_canonical_lagrangian (a : Parameters) (u : CoordinatePoint → ℝ)
    (p : CoordinatePoint) :
    sameEHScalarDensity a u p = scalarCanonicalLagrangian (sourceFactor a p)
      (massWaveNumber a ^ 2) (u p) (scalarPartial u p 0) (fun i => scalarPartial u p i.succ) := by
  rw [sameEHScalarDensity, same_eh_metric_is_scalar_conformal]
  rw [nativeRealClockDensity, scalar_conformal_native_volume,
    scalar_conformal_inverse _ p (source_factor_nonzero a p)]
  simp only [Matrix.smul_apply, smul_eq_mul]
  simp [scalarCanonicalLagrangian, metric, Matrix.diagonal_apply, Fin.sum_univ_succ]
  field_simp [source_factor_nonzero a p]
  <;> ring

theorem scalar_lagrangian_velocity_derivative (l mu2 phi v : ℝ) (P : Fin 3 → ℝ) :
    HasDerivAt (fun w : ℝ => scalarCanonicalLagrangian l mu2 phi w P)
      (scalarCanonicalMomentum l v) v := by
  have result := (((((hasDerivAt_id v).pow 2).sub_const (∑ i : Fin 3, P i ^ 2)).const_mul l).sub_const
    (mu2 * l ^ 2 * phi ^ 2)).const_mul (1 / 2 : ℝ)
  convert result using 1 <;> simp only [scalarCanonicalLagrangian, scalarCanonicalMomentum, id_eq] <;> ring

theorem scalar_lagrangian_velocity_hessian (l mu2 phi v : ℝ) (P : Fin 3 → ℝ) :
    deriv (fun w : ℝ => deriv (fun z : ℝ => scalarCanonicalLagrangian l mu2 phi z P) w) v = l := by
  have first : (fun w : ℝ => deriv (fun z : ℝ => scalarCanonicalLagrangian l mu2 phi z P) w) =
      fun w => scalarCanonicalMomentum l w :=
    funext (fun w => (scalar_lagrangian_velocity_derivative l mu2 phi w P).deriv)
  rw [first]
  simpa [scalarCanonicalMomentum] using ((hasDerivAt_id v).const_mul l).deriv

theorem same_density_scalar_regular_legendre (a : Parameters) (p : CoordinatePoint)
    (mu2 phi v pi : ℝ) (P : Fin 3 → ℝ) :
    0 < deriv (fun w : ℝ => deriv (fun z : ℝ =>
      scalarCanonicalLagrangian (sourceFactor a p) mu2 phi z P) w) v ∧
    scalarCanonicalVelocity (sourceFactor a p) (scalarCanonicalMomentum (sourceFactor a p) v) = v ∧
    scalarCanonicalMomentum (sourceFactor a p) (scalarCanonicalVelocity (sourceFactor a p) pi) = pi := by
  rw [scalar_lagrangian_velocity_hessian]
  refine ⟨source_factor_positive a p, ?_, ?_⟩
  · simp [scalarCanonicalVelocity, scalarCanonicalMomentum, source_factor_nonzero a p]
  · unfold scalarCanonicalVelocity scalarCanonicalMomentum
    field_simp [source_factor_nonzero a p]

theorem same_density_scalar_hamiltonian (l mu2 phi pi : ℝ) (P : Fin 3 → ℝ) (nonzero : l ≠ 0) :
    pi * scalarCanonicalVelocity l pi -
      scalarCanonicalLagrangian l mu2 phi (scalarCanonicalVelocity l pi) P =
        scalarCanonicalHamiltonian l mu2 phi pi P := by
  unfold scalarCanonicalVelocity scalarCanonicalLagrangian scalarCanonicalHamiltonian
  field_simp [nonzero]
  <;> ring

theorem scalar_hamiltonian_momentum_derivative (l mu2 phi pi : ℝ) (P : Fin 3 → ℝ) :
    HasDerivAt (fun z : ℝ => scalarCanonicalHamiltonian l mu2 phi z P) (pi / l) pi := by
  have result := (((((hasDerivAt_id pi).pow 2).div_const l).add_const
    (l * (∑ i : Fin 3, P i ^ 2))).add_const (mu2 * l ^ 2 * phi ^ 2)).const_mul (1 / 2 : ℝ)
  convert result using 1 <;> simp only [scalarCanonicalHamiltonian, id_eq] <;> ring

theorem scalar_hamiltonian_field_gradient_derivative (l mu2 phi pi d : ℝ)
    (P Q : Fin 3 → ℝ) :
    HasDerivAt (fun t : ℝ => scalarCanonicalHamiltonian l mu2 (phi + t * d) pi (fun i => P i + t * Q i))
      (mu2 * l ^ 2 * phi * d + l * (∑ i : Fin 3, P i * Q i)) 0 := by
  have coordinate (i : Fin 3) :
      HasDerivAt (fun t : ℝ => (P i + t * Q i) ^ 2) (2 * P i * Q i) 0 := by
    convert ((((hasDerivAt_id (0 : ℝ)).mul_const (Q i)).const_add (P i)).pow 2) using 1 <;> simp
  have sumDerivative := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => coordinate i)
  have valueDerivative : HasDerivAt (fun t : ℝ => (phi + t * d) ^ 2) (2 * phi * d) 0 := by
    convert ((((hasDerivAt_id (0 : ℝ)).mul_const d).const_add phi).pow 2) using 1 <;> simp
  have result := (((hasDerivAt_const (0 : ℝ) (pi ^ 2 / l)).add (sumDerivative.const_mul l)).add
    (valueDerivative.const_mul (mu2 * l ^ 2))).const_mul (1 / 2 : ℝ)
  have twice : (∑ i : Fin 3, 2 * P i * Q i) = 2 * ∑ i : Fin 3, P i * Q i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  convert result using 1
  rw [twice]
  ring

end AASCKleinGordon.SameActionSource
