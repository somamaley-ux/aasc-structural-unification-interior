import L2TranslationPhase
import KGFockBoundedMultipliers

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
namespace AASCKleinGordon

def bosonicPhaseMultiplier (a : Parameters) (n : ℕ) (v : ParticleConfiguration n → ℝ)
    (hv : Measurable v)
    (hi : ∀ (σ : Equiv.Perm (Fin n)) x,v (particlePermutation n σ x)=v x)
    (hbar t : ℝ) : bosonicHilbertSector a n →L[ℂ] bosonicHilbertSector a n :=
  ((Multiplication.phaseMultiplier v hv hbar t).comp (bosonicHilbertSector a n).subtypeL).codRestrict
    (bosonicHilbertSector a n) (fun f => bosonic_multiplication_output_fixed a n _
      (fun σ x => congrArg (Translation.phase hbar t) (hi σ x)) f _
      (Multiplication.phaseMultiplier_ae v hv hbar t f.val))

theorem bosonicPhaseMultiplier_norm (a : Parameters) (n : ℕ) (v : ParticleConfiguration n → ℝ)
    (hv : Measurable v)
    (hi : ∀ (σ : Equiv.Perm (Fin n)) x,v (particlePermutation n σ x)=v x)
    (hbar t : ℝ) (f : bosonicHilbertSector a n) :
    ‖bosonicPhaseMultiplier a n v hv hi hbar t f‖=‖f‖ := Multiplication.phaseMultiplier_norm v hv hbar t f.val

theorem bosonicPhaseMultiplier_zero (a : Parameters) (n : ℕ) (v : ParticleConfiguration n → ℝ)
    (hv : Measurable v)
    (hi : ∀ (σ : Equiv.Perm (Fin n)) x,v (particlePermutation n σ x)=v x)
    (hbar : ℝ) (f : bosonicHilbertSector a n) :
    bosonicPhaseMultiplier a n v hv hi hbar 0 f=f := by
  apply Subtype.ext
  exact Multiplication.phaseMultiplier_zero v hv hbar f.val

theorem bosonicPhaseMultiplier_add (a : Parameters) (n : ℕ) (v : ParticleConfiguration n → ℝ)
    (hv : Measurable v)
    (hi : ∀ (σ : Equiv.Perm (Fin n)) x,v (particlePermutation n σ x)=v x)
    (hbar t s : ℝ) (f : bosonicHilbertSector a n) :
    bosonicPhaseMultiplier a n v hv hi hbar (t+s) f=
      bosonicPhaseMultiplier a n v hv hi hbar t (bosonicPhaseMultiplier a n v hv hi hbar s f) := by
  apply Subtype.ext
  exact Multiplication.phaseMultiplier_add v hv hbar t s f.val

variable (a : Parameters) (v : ∀ n,ParticleConfiguration n → ℝ)
variable (hv : ∀ n,Measurable (v n))
variable (hi : ∀ n (σ : Equiv.Perm (Fin n)) x,v n (particlePermutation n σ x)=v n x)

def fockPhaseMultiplier (hbar t : ℝ) : FockHilbert a →L[ℂ] FockHilbert a :=
  HilbertSum.diagonal (fun n => bosonicPhaseMultiplier a n (v n) (hv n) (hi n) hbar t)
    (fun n f => (bosonicPhaseMultiplier_norm a n (v n) (hv n) (hi n) hbar t f).le)

theorem fockPhaseMultiplier_zero (hbar : ℝ) (f : FockHilbert a) :
    fockPhaseMultiplier a v hv hi hbar 0 f=f := by
  apply lp.ext
  funext n
  exact bosonicPhaseMultiplier_zero a n (v n) (hv n) (hi n) hbar (f n)

theorem fockPhaseMultiplier_add (hbar t s : ℝ) (f : FockHilbert a) :
    fockPhaseMultiplier a v hv hi hbar (t+s) f=
      fockPhaseMultiplier a v hv hi hbar t (fockPhaseMultiplier a v hv hi hbar s f) := by
  apply lp.ext
  funext n
  exact bosonicPhaseMultiplier_add a n (v n) (hv n) (hi n) hbar t s (f n)

theorem fockPhaseMultiplier_contraction (hbar t : ℝ) (f : FockHilbert a) :
    ‖fockPhaseMultiplier a v hv hi hbar t f‖≤‖f‖ := HilbertSum.diagonalLinear_norm_le _
      (fun n f => (bosonicPhaseMultiplier_norm a n (v n) (hv n) (hi n) hbar t f).le) f

theorem fockPhaseMultiplier_inverse (hbar t : ℝ) (f : FockHilbert a) :
    fockPhaseMultiplier a v hv hi hbar (-t) (fockPhaseMultiplier a v hv hi hbar t f)=f := by
  rw [← fockPhaseMultiplier_add,neg_add_cancel,fockPhaseMultiplier_zero]

theorem fockPhaseMultiplier_norm (hbar t : ℝ) (f : FockHilbert a) :
    ‖fockPhaseMultiplier a v hv hi hbar t f‖=‖f‖ := by
  apply le_antisymm (fockPhaseMultiplier_contraction a v hv hi hbar t f)
  have h := fockPhaseMultiplier_contraction a v hv hi hbar (-t)
    (fockPhaseMultiplier a v hv hi hbar t f)
  rwa [fockPhaseMultiplier_inverse] at h

def fockPhaseUnitary (hbar t : ℝ) : FockHilbert a ≃ₗᵢ[ℂ] FockHilbert a where
  toFun := fockPhaseMultiplier a v hv hi hbar t
  invFun := fockPhaseMultiplier a v hv hi hbar (-t)
  left_inv := fockPhaseMultiplier_inverse a v hv hi hbar t
  right_inv f := by
    have h := fockPhaseMultiplier_inverse a v hv hi hbar (-t) f
    simpa only [neg_neg] using h
  map_add' := (fockPhaseMultiplier a v hv hi hbar t).map_add
  map_smul' := (fockPhaseMultiplier a v hv hi hbar t).map_smul
  norm_map' := fockPhaseMultiplier_norm a v hv hi hbar t

def fockSpatialTranslation (a : Parameters) (j : Fin 3) (t : ℝ) : FockHilbert a ≃ₗᵢ[ℂ] FockHilbert a :=
  fockPhaseUnitary a (fun n => totalMomentumCLM n j) (fun n => (totalMomentumCLM n j).measurable)
    (fun n => totalMomentum_particlePermutation n j) a.hbar t

def fockTimeTranslation (a : Parameters) (t : ℝ) : FockHilbert a ≃ₗᵢ[ℂ] FockHilbert a :=
  fockPhaseUnitary a (particleTotalEnergy a) (fun n => (particleTotalEnergy_continuous a n).measurable)
    (particleTotalEnergy_particlePermutation a) a.hbar t

end AASCKleinGordon
