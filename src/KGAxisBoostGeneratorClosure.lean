import KGCoreBoostGenerator
import UnitaryInvariantCoreAdjoint
import ClosureOfEssentiallySelfAdjoint

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open scoped Topology
namespace AASCKleinGordon

theorem fockCoreAxisBoostGenerator_formally_symmetric (a : Parameters) :
    (fockCoreAxisBoostGenerator a).IsFormalAdjoint (fockCoreAxisBoostGenerator a) := by
  intro x y
  let u := (fockCoreDomainEquiv a).symm x
  let v := (fockCoreDomainEquiv a).symm y
  have hx : x=includedFockCore a u := ((fockCoreDomainEquiv a).apply_symm_apply x).symm
  have hy : y=includedFockCore a v := ((fockCoreDomainEquiv a).apply_symm_apply y).symm
  rw [hx,hy,fockCoreAxisBoostGenerator_on_original_core,fockCoreAxisBoostGenerator_on_original_core]
  exact coreAxisBoostGenerator_symmetric a u v

theorem fockCoreAxisBoostGenerator_orbit_hasDerivAt (a : Parameters)
    (x : (fockCoreAxisBoostGenerator a).domain) (r : ℝ) :
    HasDerivAt (fun s => fockAxisBoostUnitary a s x.val)
      ((axisBoostGeneratorScale a)⁻¹ • fockAxisBoostUnitary a r (fockCoreAxisBoostGenerator a x)) r := by
  let u := (fockCoreDomainEquiv a).symm x
  have hx : x=includedFockCore a u := ((fockCoreDomainEquiv a).apply_symm_apply x).symm
  rw [hx,fockCoreAxisBoostGenerator_on_original_core]
  exact fockAxisBoost_core_generator_hasDerivAt a u r

theorem fockCoreAxisBoostGenerator_commutes (a : Parameters) (r : ℝ)
    (x : (fockCoreAxisBoostGenerator a).domain) :
    fockCoreAxisBoostGenerator a
      ⟨fockAxisBoostUnitary a r x.val,fockAxisBoost_preserves_original_domain a r x⟩ =
      fockAxisBoostUnitary a r (fockCoreAxisBoostGenerator a x) := by
  apply UnitaryCore.generator_commutes_of_invariant_core
    ((axisBoostGeneratorScale a)⁻¹) (inv_ne_zero (axisBoostGeneratorScale_ne_zero a))
    (fockAxisBoostUnitary a) (fockAxisBoostUnitary_add a) (fockCoreAxisBoostGenerator a)
    (fockAxisBoost_preserves_original_domain a) ?_ r x
  intro y
  simpa only [fockAxisBoostUnitary_zero] using fockCoreAxisBoostGenerator_orbit_hasDerivAt a y 0

theorem fockAxisBoostUnitary_symm (a : Parameters) (r : ℝ) (f : FockHilbert a) :
    (fockAxisBoostUnitary a r).symm f=fockAxisBoostUnitary a (-r) f := rfl

theorem axisBoostEvolutionScale_star (a : Parameters) :
    star (-(axisBoostGeneratorScale a)⁻¹)=(axisBoostGeneratorScale a)⁻¹ := by
  change (starRingEnd ℂ) (-(axisBoostGeneratorScale a)⁻¹)=(axisBoostGeneratorScale a)⁻¹
  rw [map_neg,map_inv₀]
  change -(star (axisBoostGeneratorScale a))⁻¹=(axisBoostGeneratorScale a)⁻¹
  rw [star_axisBoostGeneratorScale,inv_neg,neg_neg]

theorem axisBoostEvolutionScale_eq_source (a : Parameters) :
    (axisBoostGeneratorScale a)⁻¹=Complex.I*((a.speed/a.hbar : ℝ) : ℂ) := by
  have hr : (a.speed/a.hbar)*(a.hbar/a.speed)=1 := by
    field_simp [a.speed_pos.ne',a.hbar_pos.ne']
  have hrc : ((a.speed/a.hbar : ℝ) : ℂ)*((a.hbar/a.speed : ℝ) : ℂ)=1 := by
    exact_mod_cast hr
  have hp : (Complex.I*((a.speed/a.hbar : ℝ) : ℂ))*axisBoostGeneratorScale a=1 := by
    calc
      _ = -(Complex.I*Complex.I)*
          (((a.speed/a.hbar : ℝ) : ℂ)*((a.hbar/a.speed : ℝ) : ℂ)) := by
            dsimp [axisBoostGeneratorScale]
            ring
      _ = 1 := by rw [Complex.I_mul_I,hrc]; norm_num
  apply mul_right_cancel₀ (axisBoostGeneratorScale_ne_zero a)
  rw [inv_mul_cancel₀ (axisBoostGeneratorScale_ne_zero a),hp]

theorem fockCoreAxisBoostGenerator_adjoint_selfAdjoint (a : Parameters) :
    IsSelfAdjoint (fockCoreAxisBoostGenerator a).adjoint :=
  UnitaryCore.adjoint_selfAdjoint_of_unitary_core _ (inv_ne_zero (axisBoostGeneratorScale_ne_zero a))
    (axisBoostEvolutionScale_star a) (fockAxisBoostUnitary a) (fockAxisBoost_strongly_continuous a)
    (fockAxisBoostUnitary_zero a) (fockAxisBoostUnitary_symm a) _
    (finiteParticleCoreToFock_dense a) (fockCoreAxisBoostGenerator_formally_symmetric a)
    (fockAxisBoost_preserves_original_domain a) (fockCoreAxisBoostGenerator_commutes a)
    (fockCoreAxisBoostGenerator_orbit_hasDerivAt a)

theorem fockCoreAxisBoostGenerator_closure_eq_adjoint (a : Parameters) :
    (fockCoreAxisBoostGenerator a).closure=(fockCoreAxisBoostGenerator a).adjoint :=
  UnitaryCore.closure_eq_adjoint_of_selfAdjoint_adjoint _ (finiteParticleCoreToFock_dense a)
    (fockCoreAxisBoostGenerator_formally_symmetric a) (fockCoreAxisBoostGenerator_adjoint_selfAdjoint a)

def fockAxisBoostGenerator (a : Parameters) : FockHilbert a →ₗ.[ℂ] FockHilbert a :=
  (fockCoreAxisBoostGenerator a).closure

theorem fockAxisBoostGenerator_selfAdjoint (a : Parameters) : IsSelfAdjoint (fockAxisBoostGenerator a) := by
  rw [fockAxisBoostGenerator,fockCoreAxisBoostGenerator_closure_eq_adjoint]
  exact fockCoreAxisBoostGenerator_adjoint_selfAdjoint a

theorem fockAxisBoost_adjoint_orbit_hasDerivAt (a : Parameters)
    (x : (fockCoreAxisBoostGenerator a).adjoint.domain) (r : ℝ) :
    HasDerivAt (fun s => fockAxisBoostUnitary a s x.val)
      ((axisBoostGeneratorScale a)⁻¹ • fockAxisBoostUnitary a r
        ((fockCoreAxisBoostGenerator a).adjoint x)) r :=
  UnitaryCore.adjoint_orbit_hasDerivAt _ (axisBoostEvolutionScale_star a)
    (fockAxisBoostUnitary a) (fockAxisBoost_strongly_continuous a) (fockAxisBoostUnitary_symm a) (fockCoreAxisBoostGenerator a)
    (finiteParticleCoreToFock_dense a) (fockAxisBoost_preserves_original_domain a)
    (fockCoreAxisBoostGenerator_commutes a) (fockCoreAxisBoostGenerator_orbit_hasDerivAt a) x r

theorem fockAxisBoost_differentiable_iff_mem_generator_domain (a : Parameters) (f : FockHilbert a) :
    DifferentiableAt ℝ (fun r => fockAxisBoostUnitary a r f) 0 ↔ f∈(fockAxisBoostGenerator a).domain := by
  rw [fockAxisBoostGenerator,fockCoreAxisBoostGenerator_closure_eq_adjoint]
  constructor
  · intro hf
    apply GlobalCharge.differentiable_orbit_mem_selfAdjoint_domain _
      (inv_ne_zero (axisBoostGeneratorScale_ne_zero a)) (axisBoostEvolutionScale_star a)
      (fockAxisBoostUnitary a) (fockAxisBoostUnitary_zero a) (fockAxisBoostUnitary_symm a)
      _ (fockCoreAxisBoostGenerator_adjoint_selfAdjoint a) ?_ f hf
    intro x
    simpa only [fockAxisBoostUnitary_zero] using fockAxisBoost_adjoint_orbit_hasDerivAt a x 0
  · intro hf
    exact (fockAxisBoost_adjoint_orbit_hasDerivAt a ⟨f,hf⟩ 0).differentiableAt

end AASCKleinGordon
