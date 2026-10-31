import WickKGOriginalUnitRaySource
import KGGeneralPoincareLocalCovariance

/-! Transport of the SAME original normal-ordered pair. The vacuum subtraction
is proved invariant from the actual field representation, not assumed. -/
noncomputable section
set_option maxHeartbeats 1500000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem wick_core_poincare_inner (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (u v : FiniteParticleCore) :
    inner ℂ (finiteParticleCoreToFock a (corePoincare a b L u))
      (finiteParticleCoreToFock a (corePoincare a b L v)) =
      inner ℂ (finiteParticleCoreToFock a u) (finiteParticleCoreToFock a v) := by
  rw [← fockPoincare_intertwines_original_core, ← fockPoincare_intertwines_original_core]
  exact (fockPoincareUnitary a b L).inner_map_map _ _

theorem wick_core_poincare_vacuum (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) : corePoincare a b L vacuumCore = vacuumCore := by
  apply finiteParticleCoreToFock_injective a
  rw [← fockPoincare_intertwines_original_core]
  exact fockPoincareUnitary_fixes_vacuum a b L

theorem wick_two_point_poincare (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (h k : 𝓢(Spacetime,ℂ)) :
    massShellTwoPointPairing a (spacetimePoincareTestCLM b L h)
      (spacetimePoincareTestCLM b L k) = massShellTwoPointPairing a h k := by
  have cov := wick_core_poincare_inner a b L vacuumCore
    (spacetimeFieldCore a 1 h (spacetimeFieldCore a 1 k vacuumCore))
  rw [spacetimeFieldCore_poincare, spacetimeFieldCore_poincare,
    wick_core_poincare_vacuum] at cov
  simpa only [spacetimePoincareTestCLM, ContinuousLinearMap.comp_apply,
    spacetimeField_vacuum_two_point, Complex.ofReal_one, one_pow, one_mul] using cov

theorem wick_normal_ordered_pair_poincare (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (h k : 𝓢(Spacetime,ℂ))
    (u : FiniteParticleCore) :
    corePoincare a b L (normalOrderedFieldPairCore a s h k u) =
      normalOrderedFieldPairCore a s (spacetimePoincareTestCLM b L h)
        (spacetimePoincareTestCLM b L k) (corePoincare a b L u) := by
  simp only [normalOrderedFieldPairCore, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul,
    wick_two_point_poincare]
  rw [spacetimeFieldCore_poincare, spacetimeFieldCore_poincare]
  rfl

theorem wick_original_pair_form_poincare (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (h k : 𝓢(Spacetime,ℂ))
    (u v : FiniteParticleCore) :
    originalPairForm a s (spacetimePoincareTestCLM b L h)
      (spacetimePoincareTestCLM b L k) (corePoincare a b L u) (corePoincare a b L v) =
      originalPairForm a s h k u v := by
  unfold originalPairForm
  rw [← wick_normal_ordered_pair_poincare]
  exact wick_core_poincare_inner a b L u _

end AASCKleinGordon
