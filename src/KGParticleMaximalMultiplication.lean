import L2RealMultiplicationSelfAdjoint
import KGFockHilbert
import KGCoreSpatialMomentum

/-! Maximal momentum and energy multiplication on the actual weighted
n-particle carrier. These are upstream of restriction to bosonic sectors
and full Fock summation. No core-closure or EMT identification is asserted. -/
noncomputable section
open MeasureTheory
namespace AASCKleinGordon

def particleTotalEnergy (a : Parameters) (n : ℕ) (x : ParticleConfiguration n) : ℝ :=
  ∑ i : Fin n, energy a (x i)

theorem particleTotalEnergy_continuous (a : Parameters) (n : ℕ) :
    Continuous (particleTotalEnergy a n) := by
  unfold particleTotalEnergy
  exact continuous_finset_sum _ (fun i _ => (energy_continuous a).comp (continuous_apply i))

theorem particleTotalEnergy_permutation (a : Parameters) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (x : ParticleConfiguration n) :
    particleTotalEnergy a n (fun i => x (σ i))=particleTotalEnergy a n x := by
  exact Equiv.sum_comp σ (fun i => energy a (x i))

theorem particleTotalEnergy_nonneg (a : Parameters) (n : ℕ) (x : ParticleConfiguration n) :
    0≤particleTotalEnergy a n x := Finset.sum_nonneg (fun i _ => (energy_pos a (x i)).le)

def particleMaximalSpatialMomentum (a : Parameters) (n : ℕ) (j : Fin 3) :
    ParticleHilbert a n →ₗ.[ℂ] ParticleHilbert a n :=
  Multiplication.realMultiplication (totalMomentumCLM n j)

def particleMaximalEnergy (a : Parameters) (n : ℕ) :
    ParticleHilbert a n →ₗ.[ℂ] ParticleHilbert a n :=
  Multiplication.realMultiplication (particleTotalEnergy a n)

theorem particleMaximalSpatialMomentum_exact_domain (a : Parameters) (n : ℕ) (j : Fin 3)
    (f : ParticleHilbert a n) :
    f ∈ (particleMaximalSpatialMomentum a n j).domain ↔
      MemLp (fun x => (totalMomentumCLM n j x : ℂ)*f x) 2 (particleMeasure a n) :=
  Multiplication.realMultiplication_exact_domain _ f

theorem particleMaximalEnergy_exact_domain (a : Parameters) (n : ℕ) (f : ParticleHilbert a n) :
    f ∈ (particleMaximalEnergy a n).domain ↔
      MemLp (fun x => (particleTotalEnergy a n x : ℂ)*f x) 2 (particleMeasure a n) :=
  Multiplication.realMultiplication_exact_domain _ f

theorem particleMaximalSpatialMomentum_selfAdjoint (a : Parameters) (n : ℕ) (j : Fin 3) :
    IsSelfAdjoint (particleMaximalSpatialMomentum a n j) :=
  Multiplication.realMultiplication_selfAdjoint _ (totalMomentumCLM n j).measurable

theorem particleMaximalEnergy_selfAdjoint (a : Parameters) (n : ℕ) :
    IsSelfAdjoint (particleMaximalEnergy a n) :=
  Multiplication.realMultiplication_selfAdjoint _ (particleTotalEnergy_continuous a n).measurable

theorem particleMaximalSpatialMomentum_closed (a : Parameters) (n : ℕ) (j : Fin 3) :
    (particleMaximalSpatialMomentum a n j).IsClosed :=
  Multiplication.realMultiplication_isClosed _ (totalMomentumCLM n j).measurable

theorem particleMaximalEnergy_closed (a : Parameters) (n : ℕ) :
    (particleMaximalEnergy a n).IsClosed :=
  Multiplication.realMultiplication_isClosed _ (particleTotalEnergy_continuous a n).measurable

theorem particleMaximalSpatialMomentum_domain_dense (a : Parameters) (n : ℕ) (j : Fin 3) :
    Dense ((particleMaximalSpatialMomentum a n j).domain : Set (ParticleHilbert a n)) :=
  Multiplication.realMultiplication_dense_domain _ (totalMomentumCLM n j).measurable

theorem particleMaximalEnergy_domain_dense (a : Parameters) (n : ℕ) :
    Dense ((particleMaximalEnergy a n).domain : Set (ParticleHilbert a n)) :=
  Multiplication.realMultiplication_dense_domain _ (particleTotalEnergy_continuous a n).measurable

end AASCKleinGordon
