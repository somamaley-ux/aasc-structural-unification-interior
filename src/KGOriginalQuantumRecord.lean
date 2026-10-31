import KGRawTensorCarrier
import WickMetricPathCovariantSourceSquare

/-! The one-KG raw carrier is the original common core in its actual Fock
embedding. Its orbit quotient is compared with the complete original record,
including every frozen request and rejection, before any endpoint claim. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum TopologicalSpace AASCSemanticExhaustion

def kgRawOriginalEquiv (a : Parameters) : WickNonzeroCore ≃ PureVector (fockCoreDomain a) where
  toFun u := ⟨fockCoreDomainEquiv a u.val,by
    intro h
    apply u.property
    apply (fockCoreDomainEquiv a).injective
    simpa only [map_zero] using h⟩
  invFun x := ⟨(fockCoreDomainEquiv a).symm x.val,by
    intro h
    apply x.property
    apply (fockCoreDomainEquiv a).symm.injective
    simpa only [map_zero] using h⟩
  left_inv u := by apply Subtype.ext; exact (fockCoreDomainEquiv a).symm_apply_apply u.val
  right_inv x := by apply Subtype.ext; exact (fockCoreDomainEquiv a).apply_symm_apply x.val

theorem kg_raw_vacuum_particle_probability (a : Parameters) :
    transitionProbability (kgRawOriginalEquiv a ⟨vacuumCore,vacuumCore_nonzero⟩)
      (kgRawOriginalEquiv a ⟨oneParticleCore,oneParticleCore_nonzero⟩)=0 := by
  have orth : inner ℂ (finiteParticleCoreToFock a vacuumCore)
      (finiteParticleCoreToFock a oneParticleCore)=0 := by
    rw [vacuumCore,oneParticleCore,finiteParticleCoreToFock_on_sector,
      finiteParticleCoreToFock_on_sector,lp.inner_single_left]
    simp [lp.single_apply]
  have numerator : ‖inner ℂ (finiteParticleCoreToFock a vacuumCore)
      (finiteParticleCoreToFock a oneParticleCore)‖^2=0 :=
    (congrArg (fun z : ℂ => ‖z‖^2) orth).trans (by norm_num)
  change ‖inner ℂ (finiteParticleCoreToFock a vacuumCore)
    (finiteParticleCoreToFock a oneParticleCore)‖^2 / _ = 0
  exact div_eq_zero_iff.mpr (Or.inl numerator)

theorem kg_raw_original_probability_nontrivial (a : Parameters) :
    ∃ x y : PureVector (fockCoreDomain a),
      transitionProbability x x=1 ∧ transitionProbability x y=0 :=
  ⟨kgRawOriginalEquiv a ⟨vacuumCore,vacuumCore_nonzero⟩,
    kgRawOriginalEquiv a ⟨oneParticleCore,oneParticleCore_nonzero⟩,
    transitionProbability_self_rep _,kg_raw_vacuum_particle_probability a⟩

theorem kg_raw_original_orbits (a : Parameters) (u v : WickNonzeroCore) :
    rayMap (fockCoreDomain a) (kgRawOriginalEquiv a u) =
      rayMap (fockCoreDomain a) (kgRawOriginalEquiv a v) ↔ wickCoreRaySetoid.r u v := by
  apply (rayMap_eq_iff (fockCoreDomain a) _ _).trans
  constructor
  · rintro ⟨c,hc,h⟩
    refine ⟨c,hc,?_⟩
    apply (fockCoreDomainEquiv a).injective
    exact h.symm.trans ((fockCoreDomainEquiv a).map_smul c u.val).symm
  · rintro ⟨c,hc,h⟩
    refine ⟨c,hc,?_⟩
    change c • fockCoreDomainEquiv a u.val = fockCoreDomainEquiv a v.val
    exact ((fockCoreDomainEquiv a).map_smul c u.val).symm.trans
      (congrArg (fockCoreDomainEquiv a) h.symm)

/-- Equality is tested on the complete original record, not only Born probes. -/
theorem kg_raw_same_original_equivalence (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u v : WickNonzeroCore) :
    rayMap (fockCoreDomain a) (kgRawOriginalEquiv a u) =
      rayMap (fockCoreDomain a) (kgRawOriginalEquiv a v) ↔
    ∀ π : WickMetricPathRoleProtocol Ω,
      wickMetricPathRoleOutput a s Ω u π=wickMetricPathRoleOutput a s Ω v π :=
  (kg_raw_original_orbits a u v).trans (wick_metric_path_record_iff_ray a s Ω u v).symm

def kgOriginalQuantumToRay (a : Parameters) :
    PhysicalRay (fockCoreDomain a) → Quotient wickCoreRaySetoid :=
  Quotient.lift (fun x => Quotient.mk wickCoreRaySetoid ((kgRawOriginalEquiv a).symm x)) (by
    intro x y h
    apply Quotient.sound
    apply (kg_raw_original_orbits a _ _).mp
    simpa only [Equiv.apply_symm_apply] using (rayMap_eq_iff _ x y).mpr h)

def kgOriginalRayToQuantum (a : Parameters) :
    Quotient wickCoreRaySetoid → PhysicalRay (fockCoreDomain a) :=
  Quotient.lift (fun u => rayMap _ (kgRawOriginalEquiv a u)) (by
    intro u v h
    exact (kg_raw_original_orbits a u v).mpr h)

def kgOriginalQuantumRayEquiv (a : Parameters) :
    PhysicalRay (fockCoreDomain a) ≃ Quotient wickCoreRaySetoid where
  toFun := kgOriginalQuantumToRay a
  invFun := kgOriginalRayToQuantum a
  left_inv r := by
    induction r using Quotient.inductionOn with
    | _ x =>
      change rayMap _ (kgRawOriginalEquiv a ((kgRawOriginalEquiv a).symm x))=rayMap _ x
      rw [Equiv.apply_symm_apply]
  right_inv r := by
    induction r using Quotient.inductionOn with
    | _ u =>
      change Quotient.mk wickCoreRaySetoid ((kgRawOriginalEquiv a).symm (kgRawOriginalEquiv a u))=_
      rw [Equiv.symm_apply_apply]

/-- Independent complete-record evaluation of the original quantum orbit.
No source equality or common-interior certificate is an input. -/
def kgOriginalQuantumRecord (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (r : PhysicalRay (fockCoreDomain a)) : WickMetricPathQresp a s Ω :=
  wickMetricPathRoleEval a s Ω (kgOriginalQuantumToRay a r)

theorem kg_original_quantum_source_square (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : PhysicalRay (fockCoreDomain a)) :
    kgOriginalQuantumRecord a s Ω r =
      (wickMetricPathF a s Ω (wickMetricPathPiA a s Ω
        (wickCommonRoleSourcePresentation a s Ω (kgOriginalQuantumToRay a r)))).val :=
  (wick_metric_path_original_source_identification a s Ω (kgOriginalQuantumToRay a r)).symm

theorem kg_original_quantum_record_on_representatives (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u : WickNonzeroCore) :
    kgOriginalQuantumRecord a s Ω (rayMap _ (kgRawOriginalEquiv a u)) =
      Quotient.mk (wickMetricPathRoleSetoid a s Ω) u := by
  change Quotient.mk (wickMetricPathRoleSetoid a s Ω)
    ((kgRawOriginalEquiv a).symm (kgRawOriginalEquiv a u))=_
  rw [Equiv.symm_apply_apply]

end AASCKleinGordon
