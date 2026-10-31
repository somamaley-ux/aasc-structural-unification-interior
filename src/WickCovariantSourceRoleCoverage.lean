import WickCovariantRayCoverage

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open TopologicalSpace
open AASCSemanticExhaustion
open scoped SchwartzMap
namespace AASCKleinGordon
attribute [local irreducible] wickCovariantOriginalCore

/-- All original protocols, including arbitrary original comparison probes,
are fixed before constructing the source receiver. -/
def wickCovariantRoleOutput (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    Quotient wickCovariantRaySetoid → WickRoleProtocol Ω → WickRoleReadout :=
  Quotient.lift (fun f => wickOriginalRoleOutput a s Ω (wickCovariantNonzeroCore a f)) (by
    intro f g h
    funext π
    exact wick_role_same_ray_entire_signature a s Ω _ _ ((wick_covariant_core_ray_iff a f g).mpr h) π)

def wickCovariantRoleEval (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (r : Quotient wickCovariantRaySetoid) : WickRoleQresp a s Ω :=
  wickOriginalRoleEval a s Ω (wickCovariantOriginalRay a r)

theorem wick_covariant_role_eval_injective (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    Function.Injective (wickCovariantRoleEval a s Ω) := by
  intro r t h
  exact wick_covariant_original_ray_injective a (wick_original_role_eval_injective a s Ω h)

theorem wick_original_role_eval_surjective (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    Function.Surjective (wickOriginalRoleEval a s Ω) := by
  intro q
  induction q using Quotient.inductionOn with | _ u =>
    exact ⟨Quotient.mk wickCoreRaySetoid u,rfl⟩

/-- This fibre uniqueness is for the ALREADY FIXED native ledger/envelope.
It is not asserted for the corpus's unrestricted source-witness type. -/
theorem wick_declared_role_forget_injective (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    Function.Injective (wickRoleForget a s Ω) := by
  intro p q h
  induction p using Quotient.inductionOn with | _ p =>
    induction q using Quotient.inductionOn with | _ q =>
      exact Quotient.sound (wick_full_role_implies_source_agreement p q (Quotient.exact h))

def wickOriginalRaySourceIndex (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (r : Quotient wickCoreRaySetoid) : WickRoleQsrc a s Ω :=
  wickRolePiA a s Ω (wickRoleSx a s Ω r)

theorem wick_original_source_presentation_normal_form (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (p : WickRoleSourcePresentation a s Ω) :
    wickOriginalRaySourceIndex a s Ω (Quotient.mk wickCoreRaySetoid p.response) =
      wickRolePiA a s Ω p := by
  exact (wick_role_source_prequotient_coherent a s Ω p.response).trans
    (Quotient.sound (wick_full_role_implies_source_agreement _ _ (fun _ => rfl)))

theorem wick_original_ray_source_index_surjective (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) : Function.Surjective (wickOriginalRaySourceIndex a s Ω) := by
  intro q
  induction q using Quotient.inductionOn with | _ p =>
    exact ⟨Quotient.mk wickCoreRaySetoid p.response,wick_original_source_presentation_normal_form a s Ω p⟩

/-- The concrete original operational presentation is formed before pi_A.
No density representative or source class is selected as input. -/
def wickCovariantSourcePresentation (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (r : Quotient wickCovariantRaySetoid) : WickRoleSourcePresentation a s Ω :=
  wickOriginalRoleSource a s Ω (wickCovariantNonzeroCore a r.out)

def wickCovariantSourceIndex (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (r : Quotient wickCovariantRaySetoid) : WickRoleQsrc a s Ω :=
  wickRolePiA a s Ω (wickCovariantSourcePresentation a s Ω r)

theorem wick_covariant_source_prequotient_square (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCovariantRaySetoid) :
    wickCovariantSourceIndex a s Ω r =
      wickOriginalRaySourceIndex a s Ω (wickCovariantOriginalRay a r) := by
  have h := wick_role_source_prequotient_coherent a s Ω (wickCovariantNonzeroCore a r.out)
  have hr : Quotient.mk wickCoreRaySetoid (wickCovariantNonzeroCore a r.out) =
      wickCovariantOriginalRay a r := congrArg (wickCovariantOriginalRay a) (Quotient.out_eq r)
  exact h.symm.trans (congrArg (wickOriginalRaySourceIndex a s Ω) hr)

theorem wick_covariant_source_base_square (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCovariantRaySetoid) :
    wickRoleForget a s Ω (wickCovariantSourceIndex a s Ω r) = wickCovariantRoleEval a s Ω r := by
  rw [wick_covariant_source_prequotient_square]
  exact wick_role_source_base_square a s Ω (wickCovariantOriginalRay a r)

theorem wick_covariant_source_index_injective (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    Function.Injective (wickCovariantSourceIndex a s Ω) := by
  intro r t h
  apply wick_covariant_role_eval_injective a s Ω
  exact (wick_covariant_source_base_square a s Ω r).symm.trans
    ((congrArg (wickRoleForget a s Ω) h).trans (wick_covariant_source_base_square a s Ω t))

theorem wick_covariant_concrete_density_square (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCovariantRaySetoid) :
    wickRoleQg a s Ω (wickCovariantSourceIndex a s Ω r) =
      wickRoleTA (wickCovariantSourcePresentation a s Ω r) := rfl

theorem wick_covariant_source_entire_output_square (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCovariantRaySetoid) (π : WickRoleProtocol Ω) :
    wickOriginalRoleOutput a s Ω (wickCovariantSourcePresentation a s Ω r).response π =
      wickCovariantRoleOutput a s Ω r π := by
  change wickCovariantRoleOutput a s Ω (Quotient.mk wickCovariantRaySetoid r.out) π = _
  rw [Quotient.out_eq]

theorem wick_covariant_source_ledger_square (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCovariantRaySetoid) :
    (wickCovariantSourcePresentation a s Ω r).ledger = wickOriginalSourceLedgerValue Ω := rfl

theorem wick_covariant_source_functional_square (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCovariantRaySetoid) (H : MetricSourceProbe Ω) :
    (wickCovariantSourcePresentation a s Ω r).attachment.functional H =
      originalWickRayMetricResponse a s Ω (wickCovariantOriginalRay a r) H := by
  have h := Quotient.exact (wick_covariant_source_prequotient_square a s Ω r)
  exact (DFunLike.congr_fun h.2.2.1 H).trans
    (wick_role_source_same_original_ray_response a s Ω (wickCovariantOriginalRay a r) H)

theorem wick_covariant_source_metric_graph (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCovariantRaySetoid)
    (H : MetricSourceProbe Ω) (z : ℝ) :
    wickRoleSourceMetResp (wickCovariantSourcePresentation a s Ω r) H z ↔
      originalWickRayMetricResponse a s Ω (wickCovariantOriginalRay a r) H = z := by
  rw [show wickRoleSourceMetResp (wickCovariantSourcePresentation a s Ω r) H z ↔
      (wickCovariantSourcePresentation a s Ω r).attachment.functional H = z from
        (wickCovariantSourcePresentation a s Ω r).attachment.source_graph H z,
    wick_covariant_source_functional_square]

theorem wick_covariant_role_finite_failure (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCovariantRaySetoid)
    (H : MetricSourceProbe Ω) (outside : H ∉ wickOriginalMetricNeighborhood Ω) :
    wickCovariantRoleOutput a s Ω r (.metric (.finite H)) = .metric .failed := by
  induction r using Quotient.inductionOn with | _ f =>
    exact congrArg WickRoleReadout.metric
      (wick_KG_original_finite_failure a s (originalWickUnitRepresentative a (wickCovariantOriginalCore a f.val)) H outside)

theorem wick_covariant_role_coverage_iff (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u : WickNonzeroCore) :
    (∃ r, wickCovariantRoleEval a s Ω r = wickRoleClassify a s Ω u) ↔
      WickOriginalOneSector u.val := by
  constructor
  · rintro ⟨r,hr⟩
    have hout : wickRoleClassify a s Ω (wickCovariantNonzeroCore a r.out) =
        wickCovariantRoleEval a s Ω r :=
      congrArg (wickCovariantRoleEval a s Ω) (Quotient.out_eq r)
    have same := wick_role_signature_separates_original_rays a s Ω _ _ (Quotient.exact (hout.trans hr))
    obtain ⟨z,_,hz⟩ := same
    rw [hz]
    exact wick_original_one_sector_smul z _ (wick_covariant_core_has_original_one_sector a r.out.val)
  · intro hu
    obtain ⟨f,hf⟩ := (wick_covariant_nonzero_core_coverage a u).mpr hu
    exact ⟨Quotient.mk wickCovariantRaySetoid f,congrArg (wickRoleClassify a s Ω) hf⟩

theorem wick_covariant_source_coverage_iff (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (p : WickRoleSourcePresentation a s Ω) :
    (∃ r, wickCovariantSourceIndex a s Ω r = wickRolePiA a s Ω p) ↔
      WickOriginalOneSector p.response.val := by
  constructor
  · rintro ⟨r,hr⟩
    apply (wick_covariant_role_coverage_iff a s Ω p.response).mp
    exact ⟨r,(wick_covariant_source_base_square a s Ω r).symm.trans (congrArg (wickRoleForget a s Ω) hr)⟩
  · intro hp
    obtain ⟨r,hr⟩ := (wick_covariant_role_coverage_iff a s Ω p.response).mpr hp
    refine ⟨r,wick_declared_role_forget_injective a s Ω ?_⟩
    exact (wick_covariant_source_base_square a s Ω r).trans hr

theorem wick_covariant_role_image_excludes_vacuum (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) :
    ¬ ∃ r, wickCovariantRoleEval a s Ω r =
      wickRoleClassify a s Ω ⟨vacuumCore,vacuumCore_nonzero⟩ := by
  intro h
  exact wick_vacuum_not_original_one_sector
    ((wick_covariant_role_coverage_iff a s Ω ⟨vacuumCore,vacuumCore_nonzero⟩).mp h)

attribute [local irreducible] originalWickRayMetricResponse wickOperationalMetricKernel

theorem wick_covariant_source_readout_is_native_kernel (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (f : WickCovariantNonzeroTest) (H : MetricSourceProbe Ω) :
    (wickCovariantSourcePresentation a s Ω (Quotient.mk wickCovariantRaySetoid f)).attachment.functional H =
      (wickOperationalMetricKernel a s H
        (wickCovariantPairTest (wickCovariantUnitTest a f.val) (wickCovariantUnitTest a f.val))).re := by
  rw [wick_covariant_source_functional_square]
  rw [show wickCovariantOriginalRay a (Quotient.mk wickCovariantRaySetoid f) =
    Quotient.mk wickCoreRaySetoid (wickCovariantNonzeroCore a f) from rfl]
  simpa only [wickCovariantNonzeroCore] using
    (wick_operational_metric_kernel_normalized_ray_readout a s H f.val f.property).symm

end AASCKleinGordon
