import KGWickCompactSmoothMetricTests

/-! Hermiticity groundwork on the SAME original core and bilocally smeared
normal-ordered pair. Local tensor Hermiticity requires the further coincidence
and test-separation argument; it is not asserted by this module. -/
noncomputable section
set_option maxHeartbeats 8000000
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

theorem original_mass_shell_pairing_conjugate (a : Parameters) (h k : 𝓢(Spacetime,ℂ)) :
    massShellTwoPointPairing a (conjugateSchwartzCLM k) (conjugateSchwartzCLM h)=
      star (massShellTwoPointPairing a h k) := by
  simp only [massShellTwoPointPairing_eq_inner,conjugateSchwartz_involutive]
  exact (inner_conj_symm _ _).symm

theorem original_normal_ordered_pair_core_adjoint (a : Parameters) (s : ℝ)
    (h k : 𝓢(Spacetime,ℂ)) (u v : FiniteParticleCore) :
    inner ℂ (finiteParticleCoreToFock a (normalOrderedFieldPairCore a s h k u))
      (finiteParticleCoreToFock a v)=
      inner ℂ (finiteParticleCoreToFock a u)
        (finiteParticleCoreToFock a
          (normalOrderedFieldPairCore a s (conjugateSchwartzCLM k) (conjugateSchwartzCLM h) v)) := by
  simp only [normalOrderedFieldPairCore,LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.smul_apply,
    LinearMap.id_coe,id_eq,map_sub,map_smul,inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right]
  rw [spacetimeFieldCore_adjoint_test a s h,spacetimeFieldCore_adjoint_test a s k,
    original_mass_shell_pairing_conjugate]
  simp [star_mul,star_pow]

theorem original_pair_form_conjugate_adjoint (a : Parameters) (s : ℝ)
    (h k : 𝓢(Spacetime,ℂ)) (u v : FiniteParticleCore) :
    star (originalPairForm a s h k u v)=
      originalPairForm a s (conjugateSchwartzCLM k) (conjugateSchwartzCLM h) v u := by
  unfold originalPairForm
  exact (inner_conj_symm _ _).trans (original_normal_ordered_pair_core_adjoint a s h k v u)

end AASCKleinGordon
