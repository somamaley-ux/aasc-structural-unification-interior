import KGNormalOrderedFieldPairs

noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

/-- Actual original bilocally smeared normal-ordered pair. This is NOT a local EMT. -/
def originalPairForm (a : Parameters) (s : ℝ) (h k : 𝓢(Spacetime,ℂ))
    (u v : FiniteParticleCore) : ℂ :=
  inner ℂ (finiteParticleCoreToFock a u)
    (finiteParticleCoreToFock a (normalOrderedFieldPairCore a s h k v))

def originalPairDiagonal (a : Parameters) (s : ℝ) (h k : 𝓢(Spacetime,ℂ))
    (u : FiniteParticleCore) : ℂ := originalPairForm a s h k u u

theorem originalPairForm_joint_state_continuous (a : Parameters) (s : ℝ)
    (h k : 𝓢(Spacetime,ℂ)) :
    Continuous (fun uv : FiniteParticleCore × FiniteParticleCore =>
      originalPairForm a s h k uv.1 uv.2) := by
  exact ((finiteParticleCoreToFock_continuous a).comp continuous_fst).inner
    ((finiteParticleCoreToFock_continuous a).comp
      ((normalOrderedFieldPairCore_state_continuous a s h k).comp continuous_snd))

theorem originalPairDiagonal_smul (a : Parameters) (s : ℝ) (h k : 𝓢(Spacetime,ℂ))
    (z : ℂ) (u : FiniteParticleCore) :
    originalPairDiagonal a s h k (z • u)=(‖z‖^2 : ℝ) • originalPairDiagonal a s h k u := by
  simp only [originalPairDiagonal,originalPairForm,map_smul,inner_smul_left,inner_smul_right,
    ← mul_assoc,starRingEnd_apply]
  rw [show z*star z=(‖z‖ : ℂ)^2 from Complex.mul_conj' z]
  rw [← Complex.ofReal_pow]
  rfl

theorem originalPairDiagonal_parallelogram (a : Parameters) (s : ℝ)
    (h k : 𝓢(Spacetime,ℂ)) (u v : FiniteParticleCore) :
    originalPairDiagonal a s h k (u+v)+originalPairDiagonal a s h k (u-v)=
      2*originalPairDiagonal a s h k u+2*originalPairDiagonal a s h k v := by
  simp only [originalPairDiagonal,originalPairForm,map_add,map_sub,
    inner_add_left,inner_add_right,inner_sub_left,inner_sub_right]
  ring

theorem originalPairDiagonal_polarization (a : Parameters) (s : ℝ)
    (h k : 𝓢(Spacetime,ℂ)) (u v : FiniteParticleCore) :
    4*originalPairForm a s h k u v=
      originalPairDiagonal a s h k (u+v)-originalPairDiagonal a s h k (u-v)-
        Complex.I*originalPairDiagonal a s h k (u+Complex.I • v)+
          Complex.I*originalPairDiagonal a s h k (u-Complex.I • v) := by
  have hI : (starRingEnd ℂ) Complex.I = -Complex.I := by simp
  have hsI : star Complex.I = -Complex.I := by simp
  simp only [originalPairDiagonal,originalPairForm,map_add,map_sub,map_smul,
    inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,
    inner_smul_left,inner_smul_right,hI,hsI]
  ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem originalPairDiagonal_phase_invariant (a : Parameters) (s : ℝ)
    (h k : 𝓢(Spacetime,ℂ)) (z : ℂ) (hz : ‖z‖=1) (u : FiniteParticleCore) :
    originalPairDiagonal a s h k (z • u)=originalPairDiagonal a s h k u := by
  rw [originalPairDiagonal_smul,hz,one_pow,one_smul]

theorem originalPairDiagonal_vacuum_baseline (a : Parameters) (s : ℝ)
    (h k : 𝓢(Spacetime,ℂ)) : originalPairDiagonal a s h k vacuumCore=0 :=
  normalOrderedFieldPairCore_vacuum_mean_zero a s h k

end AASCKleinGordon
