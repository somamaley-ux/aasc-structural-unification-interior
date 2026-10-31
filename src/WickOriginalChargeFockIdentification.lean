import WickOriginalFourChannelCharge
import WickOriginalFockMomentum
import WickOriginalEnergyActivity

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace AASCKleinGordon

theorem wick_original_hypersurface_charge_fock_inner (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (j : Fin 4) (τ : ℝ) :
    wickOriginalHypersurfaceCharge a s u v j τ=
      wickSameTensorChargeCoefficient a s*
        inner ℂ (finiteParticleCoreToFock a u)
          (finiteParticleCoreToFock a (wickOriginalCoreFourMomentum a j v)) := by
  rw [wick_original_hypersurface_charge_cutoff,wick_original_four_momentum_joint_cutoff]
  simp only [Nat.cast_add,Nat.cast_one,Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one]

def wickOriginalStressChargeCore (a : Parameters) (s : ℝ) (j : Fin 4) :
    FiniteParticleCore →ₗ[ℂ] FiniteParticleCore :=
  wickSameTensorChargeCoefficient a s • wickOriginalCoreFourMomentum a j

theorem wick_original_hypersurface_charge_core_pairing (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (j : Fin 4) (τ : ℝ) :
    wickOriginalHypersurfaceCharge a s u v j τ=
      inner ℂ (finiteParticleCoreToFock a u)
        (finiteParticleCoreToFock a (wickOriginalStressChargeCore a s j v)) := by
  rw [wick_original_hypersurface_charge_fock_inner]
  change _=inner ℂ (finiteParticleCoreToFock a u)
    (finiteParticleCoreToFock a (wickSameTensorChargeCoefficient a s •
      wickOriginalCoreFourMomentum a j v))
  rw [map_smul,inner_smul_right]

/-- The vector representing the actual integrated stress form is unique on
the SAME full Hilbert Fock carrier because the original core is dense. -/
theorem wick_original_hypersurface_charge_unique_vector (a : Parameters) (s : ℝ)
    (v : FiniteParticleCore) (j : Fin 4) (τ : ℝ) (z : FockHilbert a)
    (represents : ∀ u,inner ℂ (finiteParticleCoreToFock a u) z=
      wickOriginalHypersurfaceCharge a s u v j τ) :
    z=finiteParticleCoreToFock a (wickOriginalStressChargeCore a s j v) := by
  let y := finiteParticleCoreToFock a (wickOriginalStressChargeCore a s j v)
  have same : (fun w : FockHilbert a => inner ℂ w z)=(fun w => inner ℂ w y) :=
    (finiteParticleCoreToFock_dense a).equalizer
      (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
      (funext (fun u => (represents u).trans
        (wick_original_hypersurface_charge_core_pairing a s u v j τ)))
  have hzero : inner ℂ (z-y) (z-y)=0 := by
    rw [inner_sub_right]
    exact sub_eq_zero.mpr (congrFun same (z-y))
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)

def wickOriginalStressCharge (a : Parameters) (s : ℝ) (j : Fin 4) :
    FockHilbert a →ₗ.[ℂ] FockHilbert a where
  domain := fockCoreDomain a
  toFun := ((finiteParticleCoreToFock a).comp (wickOriginalStressChargeCore a s j)).comp
    (fockCoreDomainEquiv a).symm.toLinearMap

theorem wick_original_stress_charge_on_core (a : Parameters) (s : ℝ) (j : Fin 4)
    (v : FiniteParticleCore) :
    wickOriginalStressCharge a s j (includedFockCore a v)=
      finiteParticleCoreToFock a (wickOriginalStressChargeCore a s j v) := by
  change finiteParticleCoreToFock a (wickOriginalStressChargeCore a s j
    ((fockCoreDomainEquiv a).symm (fockCoreDomainEquiv a v)))=_
  rw [LinearEquiv.symm_apply_apply]

theorem wick_original_stress_charge_domain_dense (a : Parameters) (s : ℝ) (j : Fin 4) :
    Dense ((wickOriginalStressCharge a s j).domain : Set (FockHilbert a)) :=
  finiteParticleCoreToFock_dense a

theorem wick_original_stress_charge_hypersurface_pairing (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (j : Fin 4) (τ : ℝ) :
    inner ℂ (finiteParticleCoreToFock a u)
      (wickOriginalStressCharge a s j (includedFockCore a v))=
        wickOriginalHypersurfaceCharge a s u v j τ := by
  rw [wick_original_stress_charge_on_core]
  exact (wick_original_hypersurface_charge_core_pairing a s u v j τ).symm

end AASCKleinGordon
