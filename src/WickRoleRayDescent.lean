import WickOriginalRoleLedger

noncomputable section
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem wick_role_normalized_phase (a : Parameters) (u v : WickNonzeroCore)
    (same : wickCoreRaySetoid.r u v) :
    ∃ z : ℂ, ‖z‖=1 ∧ originalWickUnitRepresentative a v.val=
      z • originalWickUnitRepresentative a u.val := by
  have unitSame : wickCoreRaySetoid.r (originalWickUnitNonzeroRepresentative a u)
      (originalWickUnitNonzeroRepresentative a v) :=
    Quotient.exact ((original_wick_unit_representative_same_ray a u).trans
      ((Quotient.sound same).trans (original_wick_unit_representative_same_ray a v).symm))
  obtain ⟨z,_,equal⟩ := unitSame
  change originalWickUnitRepresentative a v.val=z • originalWickUnitRepresentative a u.val at equal
  refine ⟨z,?_,equal⟩
  have norms := original_wick_unit_representative_norm a v.val v.property
  rw [equal,map_smul,norm_smul,original_wick_unit_representative_norm a u.val u.property,mul_one] at norms
  exact norms

theorem wick_role_comparison_phase_invariant (a : Parameters) (u v : WickNonzeroCore)
    (same : wickCoreRaySetoid.r u v) (g : ProperPoincareTransform) (probe : WickNonzeroCore) :
    wickOriginalRoleComparison a u probe g=wickOriginalRoleComparison a v probe g := by
  obtain ⟨z,hz,equal⟩ := wick_role_normalized_phase a u v same
  simp only [wickOriginalRoleComparison,equal,map_smul,inner_smul_right,norm_mul,hz,one_mul]

theorem wick_role_same_ray_entire_signature (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u v : WickNonzeroCore) (same : wickCoreRaySetoid.r u v) :
    (wickOriginalRoleSetoid a s Ω).r u v := by
  intro π
  cases π with
  | metric π =>
    exact congrArg WickRoleReadout.metric
      (wick_KG_original_normalized_prequotient_readouts a s u v same π)
  | comparison g probe =>
    exact congrArg WickRoleReadout.probability
      (wick_role_comparison_phase_invariant a u v same g probe)

theorem wick_role_signature_separates_original_rays (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u v : WickNonzeroCore)
    (same : (wickOriginalRoleSetoid a s Ω).r u v) : wickCoreRaySetoid.r u v := by
  let U := finiteParticleCoreToFock a (originalWickUnitRepresentative a u.val)
  let V := finiteParticleCoreToFock a (originalWickUnitRepresentative a v.val)
  have nu : ‖U‖=1 := original_wick_unit_representative_norm a u.val u.property
  have nv : ‖V‖=1 := original_wick_unit_representative_norm a v.val v.property
  have nzU : U≠0 := norm_ne_zero_iff.mp (by rw [nu];norm_num)
  have nzV : V≠0 := norm_ne_zero_iff.mp (by rw [nv];norm_num)
  have equality := wick_role_equivalence_transport_comparisons a s Ω u v same 1 u
  simp only [wickOriginalRoleComparison,map_one] at equality
  have self : ‖inner ℂ U U‖=1 := by rw [inner_self_eq_norm_sq_to_K, norm_pow];simp [nu]
  have amp : ‖inner ℂ U V‖=‖U‖*‖V‖ := by
    change ‖inner ℂ U U‖^2=‖inner ℂ U V‖^2 at equality
    rw [self] at equality
    rw [nu,nv]
    nlinarith [norm_nonneg (inner ℂ U V)]
  obtain ⟨z,hz,scale⟩ := (norm_inner_eq_norm_iff nzU nzV).mp amp
  have core : originalWickUnitRepresentative a v.val=z • originalWickUnitRepresentative a u.val :=
    finiteParticleCoreToFock_injective a (scale.trans (map_smul _ _ _).symm)
  have unitRelation : wickCoreRaySetoid.r (originalWickUnitNonzeroRepresentative a u)
      (originalWickUnitNonzeroRepresentative a v) := ⟨z,hz,core⟩
  exact Quotient.exact ((original_wick_unit_representative_same_ray a u).symm.trans
    ((Quotient.sound unitRelation).trans (original_wick_unit_representative_same_ray a v)))

theorem wick_role_signature_iff_original_ray (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u v : WickNonzeroCore) :
    (wickOriginalRoleSetoid a s Ω).r u v ↔ wickCoreRaySetoid.r u v :=
  ⟨wick_role_signature_separates_original_rays a s Ω u v,
    wick_role_same_ray_entire_signature a s Ω u v⟩

/-- Independent state evaluation in the full original declared response
signature. No metric functional or density is used in this definition. -/
def wickOriginalRoleEval (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    Quotient wickCoreRaySetoid → WickRoleQresp a s Ω :=
  Quotient.map id (fun u v same => wick_role_same_ray_entire_signature a s Ω u v same)

theorem wick_original_role_eval_injective (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) : Function.Injective (wickOriginalRoleEval a s Ω) := by
  intro r t equal
  induction r using Quotient.inductionOn with | _ u =>
    induction t using Quotient.inductionOn with | _ v =>
      exact Quotient.sound (wick_role_signature_separates_original_rays a s Ω u v (Quotient.exact equal))

end AASCKleinGordon
