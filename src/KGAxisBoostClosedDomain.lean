import KGAxisBoostGeneratorClosure

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open scoped Topology
namespace AASCKleinGordon

theorem fockAxisBoostGenerator_orbit_hasDerivAt (a : Parameters)
    (x : (fockAxisBoostGenerator a).domain) (r : ℝ) :
    HasDerivAt (fun t => fockAxisBoostUnitary a t x.val)
      ((axisBoostGeneratorScale a)⁻¹ • fockAxisBoostUnitary a r (fockAxisBoostGenerator a x)) r := by
  revert x
  rw [fockAxisBoostGenerator,fockCoreAxisBoostGenerator_closure_eq_adjoint]
  intro x
  exact fockAxisBoost_adjoint_orbit_hasDerivAt a x r

theorem fockAxisBoostGenerator_preserves_domain (a : Parameters) (r : ℝ)
    (x : (fockAxisBoostGenerator a).domain) :
    fockAxisBoostUnitary a r x.val∈(fockAxisBoostGenerator a).domain := by
  apply (fockAxisBoost_differentiable_iff_mem_generator_domain a _).mp
  have h := ((fockAxisBoostUnitary a r).toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ).differentiableAt.comp 0 (fockAxisBoostGenerator_orbit_hasDerivAt a x 0).differentiableAt
  have he : (fun t : ℝ => fockAxisBoostUnitary a r (fockAxisBoostUnitary a t x.val)) =
      (fun t : ℝ => fockAxisBoostUnitary a t (fockAxisBoostUnitary a r x.val)) := by
    funext t
    rw [fockAxisBoostUnitary_add,fockAxisBoostUnitary_add,add_comm]
  change DifferentiableAt ℝ (fun t : ℝ => fockAxisBoostUnitary a r (fockAxisBoostUnitary a t x.val)) 0 at h
  rw [he] at h
  exact h

theorem fockAxisBoostGenerator_commutes (a : Parameters) (r : ℝ)
    (x : (fockAxisBoostGenerator a).domain) :
    fockAxisBoostGenerator a
      ⟨fockAxisBoostUnitary a r x.val,fockAxisBoostGenerator_preserves_domain a r x⟩ =
      fockAxisBoostUnitary a r (fockAxisBoostGenerator a x) := by
  apply UnitaryCore.generator_commutes_of_invariant_core
    ((axisBoostGeneratorScale a)⁻¹) (inv_ne_zero (axisBoostGeneratorScale_ne_zero a))
    (fockAxisBoostUnitary a) (fockAxisBoostUnitary_add a) (fockAxisBoostGenerator a)
    (fockAxisBoostGenerator_preserves_domain a) ?_ r x
  intro y
  simpa only [fockAxisBoostUnitary_zero] using fockAxisBoostGenerator_orbit_hasDerivAt a y 0

end AASCKleinGordon
