import KGBosonicMultiplicationInvariance
import L2SubspaceRealMultiplication
import KGParticleMaximalMultiplication

noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Filter
namespace AASCKleinGordon

def bosonicRealMultiplication (a : Parameters) (n : ℕ)
    (v : ParticleConfiguration n → ℝ) (hv : Measurable v)
    (hi : ∀ (σ : Equiv.Perm (Fin n)) x,v (particlePermutation n σ x)=v x) :
    bosonicHilbertSector a n →ₗ.[ℂ] bosonicHilbertSector a n :=
  Multiplication.subspaceRealMultiplication v hv (bosonicHilbertSector a n)
    (particleGraphBoundedA_preserves_bosonic a n v hv hi)
    (particleGraphBoundedB_preserves_bosonic a n v hv hi)

theorem bosonicRealMultiplication_mem_graph (a : Parameters) (n : ℕ)
    (v : ParticleConfiguration n → ℝ) (hv : Measurable v)
    (hi : ∀ (σ : Equiv.Perm (Fin n)) x,v (particlePermutation n σ x)=v x)
    (f g : bosonicHilbertSector a n) :
    (f,g) ∈ (bosonicRealMultiplication a n v hv hi).graph ↔
      g.val=ᵐ[particleMeasure a n] (fun x => (v x : ℂ)*f.val x) :=
  Multiplication.subspaceRealMultiplication_mem_graph _ _ _ _ _ f g

theorem bosonicRealMultiplication_exact_domain (a : Parameters) (n : ℕ)
    (v : ParticleConfiguration n → ℝ) (hv : Measurable v)
    (hi : ∀ (σ : Equiv.Perm (Fin n)) x,v (particlePermutation n σ x)=v x)
    (f : bosonicHilbertSector a n) :
    f ∈ (bosonicRealMultiplication a n v hv hi).domain ↔
      MemLp (fun x => (v x : ℂ)*f.val x) 2 (particleMeasure a n) := by
  constructor
  · intro hf
    let g := bosonicRealMultiplication a n v hv hi ⟨f,hf⟩
    have hg := (bosonicRealMultiplication_mem_graph a n v hv hi f g).1
      ((bosonicRealMultiplication a n v hv hi).mem_graph ⟨f,hf⟩)
    exact (Lp.memLp g.val).ae_eq hg
  · intro hf
    let g : ParticleHilbert a n := hf.toLp _
    have hgf : g=ᵐ[particleMeasure a n] (fun x => (v x : ℂ)*f.val x) := hf.coeFn_toLp
    have hg : g ∈ bosonicHilbertSector a n := bosonic_multiplication_output_fixed a n _
      (fun σ x => congrArg Complex.ofReal (hi σ x)) f g hgf
    exact LinearPMap.mem_domain_of_mem_graph
      ((bosonicRealMultiplication_mem_graph a n v hv hi f ⟨g,hg⟩).2 hgf)

theorem bosonicRealMultiplication_selfAdjoint (a : Parameters) (n : ℕ)
    (v : ParticleConfiguration n → ℝ) (hv : Measurable v)
    (hi : ∀ (σ : Equiv.Perm (Fin n)) x,v (particlePermutation n σ x)=v x) :
    IsSelfAdjoint (bosonicRealMultiplication a n v hv hi) :=
  Multiplication.subspaceRealMultiplication_selfAdjoint _ _ _ _ _

theorem bosonicRealMultiplication_closed (a : Parameters) (n : ℕ)
    (v : ParticleConfiguration n → ℝ) (hv : Measurable v)
    (hi : ∀ (σ : Equiv.Perm (Fin n)) x,v (particlePermutation n σ x)=v x) :
    (bosonicRealMultiplication a n v hv hi).IsClosed :=
  Multiplication.subspaceRealMultiplication_closed _ _ _ _ _

theorem bosonicRealMultiplication_dense (a : Parameters) (n : ℕ)
    (v : ParticleConfiguration n → ℝ) (hv : Measurable v)
    (hi : ∀ (σ : Equiv.Perm (Fin n)) x,v (particlePermutation n σ x)=v x) :
    Dense ((bosonicRealMultiplication a n v hv hi).domain : Set (bosonicHilbertSector a n)) :=
  Multiplication.subspaceRealMultiplication_dense _ _ _ _ _

def bosonicMaximalSpatialMomentum (a : Parameters) (n : ℕ) (j : Fin 3) :
    bosonicHilbertSector a n →ₗ.[ℂ] bosonicHilbertSector a n :=
  bosonicRealMultiplication a n (totalMomentumCLM n j) (totalMomentumCLM n j).measurable
    (totalMomentum_particlePermutation n j)

theorem particleTotalEnergy_particlePermutation (a : Parameters) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (x : ParticleConfiguration n) :
    particleTotalEnergy a n (particlePermutation n σ x)=particleTotalEnergy a n x := by
  have he : particlePermutation n σ x=(fun i => x (σ.symm i)) :=
    funext (particlePermutation_apply n σ x)
  rw [he]
  exact particleTotalEnergy_permutation a n σ.symm x

def bosonicMaximalEnergy (a : Parameters) (n : ℕ) :
    bosonicHilbertSector a n →ₗ.[ℂ] bosonicHilbertSector a n :=
  bosonicRealMultiplication a n (particleTotalEnergy a n) (particleTotalEnergy_continuous a n).measurable
    (particleTotalEnergy_particlePermutation a n)

theorem bosonicMaximalSpatialMomentum_selfAdjoint (a : Parameters) (n : ℕ) (j : Fin 3) :
    IsSelfAdjoint (bosonicMaximalSpatialMomentum a n j) := bosonicRealMultiplication_selfAdjoint _ _ _ _ _

theorem bosonicMaximalEnergy_selfAdjoint (a : Parameters) (n : ℕ) :
    IsSelfAdjoint (bosonicMaximalEnergy a n) := bosonicRealMultiplication_selfAdjoint _ _ _ _ _

theorem bosonicMaximalSpatialMomentum_graph_on_original_core
    (a : Parameters) (n : ℕ) (j : Fin 3) (f : bosonicSchwartz n) :
    (bosonicCoreToSector a n f,bosonicCoreToSector a n (sectorSpatialMomentum n j f)) ∈
      (bosonicMaximalSpatialMomentum a n j).graph := by
  apply (bosonicRealMultiplication_mem_graph _ _ _ _ _ _ _).2
  have h1 := (schwartzTotalMomentum n j f.val).coeFn_toLp 2 (particleMeasure a n)
  have h2 := f.val.coeFn_toLp 2 (particleMeasure a n)
  filter_upwards [h1,h2] with x hx hy
  change ((schwartzTotalMomentum n j f.val).toLp 2 (particleMeasure a n)) x=
    (totalMomentumCLM n j x : ℂ)*(f.val.toLp 2 (particleMeasure a n)) x
  rw [hx,hy,schwartzTotalMomentum_apply]

end AASCKleinGordon
