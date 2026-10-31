import WickCovariantSourceRoleCoverage

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open TopologicalSpace
open AASCSemanticExhaustion
open scoped SchwartzMap
namespace AASCKleinGordon

/-- The actual original sector operations, expressed in covariant test
coordinates using the independently proved sector inverse. -/
def wickCovariantPoincareTest (a : Parameters) (q : ProperPoincareTransform)
    (f : 𝓢(Momentum,ℂ)) : 𝓢(Momentum,ℂ) :=
  wickCovariantSectorCoordinates a
    (bosonicEventTranslationSchwartzCLM a 1 q.left.toAdd
      (bosonicLorentzSchwartzCLM a 1 q.right (wickCovariantOriginalSector a f)))

theorem wick_covariant_core_poincare_square (a : Parameters) (q : ProperPoincareTransform)
    (f : 𝓢(Momentum,ℂ)) :
    wickCovariantOriginalCore a (wickCovariantPoincareTest a q f) =
      corePoincare a q.left.toAdd q.right (wickCovariantOriginalCore a f) := by
  change wickOneCoreCLM (wickCovariantOriginalSector a (wickCovariantSectorCoordinates a _)) = _
  rw [wick_covariant_sector_coordinates_right]
  change DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) 1 _ =
    coreEventTranslation a q.left.toAdd
      (coreLorentz a q.right (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) 1 _))
  rw [coreLorentz_lof,coreEventTranslation_lof]
  rfl

theorem wick_original_one_sector_poincare (a : Parameters) (q : ProperPoincareTransform)
    (u : FiniteParticleCore) (hu : WickOriginalOneSector u) :
    WickOriginalOneSector (corePoincare a q.left.toAdd q.right u) := by
  obtain ⟨f,rfl⟩ := (wick_covariant_core_coverage_iff a u).mpr hu
  rw [← wick_covariant_core_poincare_square]
  exact wick_covariant_core_has_original_one_sector a _

theorem wick_covariant_poincare_test_nonzero (a : Parameters) (q : ProperPoincareTransform)
    (f : 𝓢(Momentum,ℂ)) (hf : f ≠ 0) : wickCovariantPoincareTest a q f ≠ 0 := by
  intro hz
  apply wick_covariant_original_core_nonzero a f hf
  apply (corePoincareEquiv a q.left.toAdd q.right).injective
  change corePoincare a q.left.toAdd q.right (wickCovariantOriginalCore a f) =
    corePoincare a q.left.toAdd q.right 0
  rw [← wick_covariant_core_poincare_square,hz,map_zero,map_zero]

theorem wick_covariant_poincare_test_smul (a : Parameters) (q : ProperPoincareTransform)
    (c : ℂ) (f : 𝓢(Momentum,ℂ)) :
    wickCovariantPoincareTest a q (c • f) = c • wickCovariantPoincareTest a q f := by
  apply wick_covariant_original_core_injective a
  simp only [wick_covariant_core_poincare_square,map_smul]

theorem wick_covariant_poincare_test_mul (a : Parameters) (q r : ProperPoincareTransform)
    (f : 𝓢(Momentum,ℂ)) :
    wickCovariantPoincareTest a q (wickCovariantPoincareTest a r f) =
      wickCovariantPoincareTest a (q*r) f := by
  apply wick_covariant_original_core_injective a
  calc
    _ = corePoincare a q.left.toAdd q.right
        (wickCovariantOriginalCore a (wickCovariantPoincareTest a r f)) :=
      wick_covariant_core_poincare_square a q _
    _ = corePoincare a q.left.toAdd q.right
        (corePoincare a r.left.toAdd r.right (wickCovariantOriginalCore a f)) :=
      congrArg (corePoincare a q.left.toAdd q.right) (wick_covariant_core_poincare_square a r f)
    _ = corePoincare a (q.left.toAdd+spacetimeLorentzCLE q.right r.left.toAdd)
        (q.right*r.right) (wickCovariantOriginalCore a f) := corePoincare_mul a _ _ _ _ _
    _ = wickCovariantOriginalCore a (wickCovariantPoincareTest a (q*r) f) :=
      (wick_covariant_core_poincare_square a (q*r) f).symm

def wickCovariantPoincareNonzero (a : Parameters) (q : ProperPoincareTransform)
    (f : WickCovariantNonzeroTest) : WickCovariantNonzeroTest :=
  ⟨wickCovariantPoincareTest a q f.val,wick_covariant_poincare_test_nonzero a q f.val f.property⟩

def wickCovariantPoincareRay (a : Parameters) (q : ProperPoincareTransform) :
    Quotient wickCovariantRaySetoid → Quotient wickCovariantRaySetoid :=
  Quotient.map (wickCovariantPoincareNonzero a q) (by
    rintro f g ⟨z,hz,h⟩
    exact ⟨z,hz,(congrArg (wickCovariantPoincareTest a q) h).trans
      (wick_covariant_poincare_test_smul a q z f.val)⟩)

theorem wick_covariant_nonzero_core_poincare (a : Parameters) (q : ProperPoincareTransform)
    (f : WickCovariantNonzeroTest) :
    wickCovariantNonzeroCore a (wickCovariantPoincareNonzero a q f) =
      wickPoincareNonzeroCore a q.left.toAdd q.right (wickCovariantNonzeroCore a f) :=
  Subtype.ext (wick_covariant_core_poincare_square a q f.val)

theorem wick_covariant_original_ray_poincare (a : Parameters) (q : ProperPoincareTransform)
    (r : Quotient wickCovariantRaySetoid) :
    wickCovariantOriginalRay a (wickCovariantPoincareRay a q r) =
      wickPoincareRayAction a q.left.toAdd q.right (wickCovariantOriginalRay a r) := by
  induction r using Quotient.inductionOn with | _ f =>
    exact congrArg (Quotient.mk wickCoreRaySetoid) (wick_covariant_nonzero_core_poincare a q f)

theorem wick_unitary_representation_conjugate_apply {G E : Type*} [Group G]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ρ : G →* (E ≃ₗᵢ[ℂ] E)) (q g : G) (u : E) :
    ρ (q*g*q⁻¹) (ρ q u) = ρ q (ρ g u) := by
  calc
    _ = ρ ((q*g*q⁻¹)*q) u :=
      (congrArg (fun e : E ≃ₗᵢ[ℂ] E => e u) (ρ.map_mul (q*g*q⁻¹) q)).symm
    _ = ρ (q*g) u := by rw [mul_assoc,inv_mul_cancel,mul_one]
    _ = ρ q (ρ g u) := congrArg (fun e : E ≃ₗᵢ[ℂ] E => e u) (ρ.map_mul q g)

theorem wick_original_unit_fock_poincare (a : Parameters) (q : ProperPoincareTransform)
    (u : FiniteParticleCore) :
    finiteParticleCoreToFock a (originalWickUnitRepresentative a (corePoincare a q.left.toAdd q.right u)) =
      originalFockPoincareRepresentation a q (finiteParticleCoreToFock a (originalWickUnitRepresentative a u)) := by
  rw [wick_unit_representative_poincare]
  exact (fockPoincare_intertwines_original_core a q.left.toAdd q.right _).symm

theorem wick_original_role_comparison_poincare (a : Parameters) (q g : ProperPoincareTransform)
    (u v : WickNonzeroCore) :
    wickOriginalRoleComparison a (wickPoincareNonzeroCore a q.left.toAdd q.right u)
      (wickPoincareNonzeroCore a q.left.toAdd q.right v) (q*g*q⁻¹) =
        wickOriginalRoleComparison a u v g := by
  change ‖inner ℂ
    (finiteParticleCoreToFock a (originalWickUnitRepresentative a (corePoincare a q.left.toAdd q.right v.val)))
    (originalFockPoincareRepresentation a (q*g*q⁻¹)
      (finiteParticleCoreToFock a (originalWickUnitRepresentative a (corePoincare a q.left.toAdd q.right u.val))))‖^2 = _
  rw [wick_original_unit_fock_poincare,wick_original_unit_fock_poincare,
    wick_unitary_representation_conjugate_apply]
  rw [(originalFockPoincareRepresentation a q).inner_map_map]
  rfl

def wickCovariantRoleProtocolTransport (a : Parameters) (q : ProperPoincareTransform)
    {Ω : Opens CoordinatePoint} : WickRoleProtocol Ω →
      WickRoleProtocol (wickAffineMetricRegion q.left.toAdd q.right Ω)
  | .metric π => .metric (wickKGProtocolPoincare q.left.toAdd q.right π)
  | .comparison g v => .comparison (q*g*q⁻¹) (wickPoincareNonzeroCore a q.left.toAdd q.right v)

/-- The finite admission chart is transported together with its requests;
it is not silently replaced by a fresh coordinate-box neighborhood. -/
def wickCovariantTransportedRoleOutput (a : Parameters) (s : ℝ) (q : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCovariantRaySetoid) :
    WickRoleProtocol (wickAffineMetricRegion q.left.toAdd q.right Ω) → WickRoleReadout
  | .metric π => .metric (wickKGTransportedRayOutput a s q.left.toAdd q.right Ω
      (wickCovariantOriginalRay a r) π)
  | .comparison g v => wickCovariantRoleOutput a s
      (wickAffineMetricRegion q.left.toAdd q.right Ω) r (.comparison g v)

theorem wick_covariant_role_metric_ray_output (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : Quotient wickCovariantRaySetoid) (π : WickKGOriginalProtocol Ω) :
    wickCovariantRoleOutput a s Ω r (.metric π) =
      .metric (wickKGOriginalRayOutput a s Ω (wickCovariantOriginalRay a r) π) := by
  induction r using Quotient.inductionOn with | _ f => rfl

theorem wick_covariant_entire_role_poincare (a : Parameters) (s : ℝ)
    (q : ProperPoincareTransform) (Ω : Opens CoordinatePoint)
    (r : Quotient wickCovariantRaySetoid) (π : WickRoleProtocol Ω) :
    wickCovariantTransportedRoleOutput a s q Ω (wickCovariantPoincareRay a q r)
      (wickCovariantRoleProtocolTransport a q π) = wickCovariantRoleOutput a s Ω r π := by
  cases π with
  | metric π =>
    change WickRoleReadout.metric (wickKGTransportedRayOutput a s q.left.toAdd q.right Ω
      (wickCovariantOriginalRay a (wickCovariantPoincareRay a q r))
      (wickKGProtocolPoincare q.left.toAdd q.right π)) = _
    rw [wick_covariant_original_ray_poincare,wick_KG_entire_ray_family_poincare,
      wick_covariant_role_metric_ray_output]
  | comparison g v =>
    induction r using Quotient.inductionOn with | _ f =>
      apply congrArg WickRoleReadout.probability
      change wickOriginalRoleComparison a
        (wickCovariantNonzeroCore a (wickCovariantPoincareNonzero a q f))
        (wickPoincareNonzeroCore a q.left.toAdd q.right v) (q*g*q⁻¹) = _
      rw [wick_covariant_nonzero_core_poincare]
      exact wick_original_role_comparison_poincare a q g _ v

theorem wick_covariant_metric_admission_transport (q : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω) :
    wickNativeAffineMetricTest q.left.toAdd q.right H ∈
      wickTransportedMetricDomain q.left.toAdd q.right Ω ↔ H ∈ wickOriginalMetricNeighborhood Ω :=
  wick_transported_metric_domain_exact q.left.toAdd q.right Ω H

theorem wick_covariant_source_functional_poincare (a : Parameters) (s : ℝ)
    (q : ProperPoincareTransform) (Ω : Opens CoordinatePoint)
    (r : Quotient wickCovariantRaySetoid) (H : MetricSourceProbe Ω) :
    (wickCovariantSourcePresentation a s (wickAffineMetricRegion q.left.toAdd q.right Ω)
      (wickCovariantPoincareRay a q r)).attachment.functional
      (wickNativeAffineMetricTest q.left.toAdd q.right H) =
        (wickCovariantSourcePresentation a s Ω r).attachment.functional H := by
  rw [wick_covariant_source_functional_square,wick_covariant_source_functional_square,
    wick_covariant_original_ray_poincare]
  exact wick_original_ray_source_poincare a q.left.toAdd q.right s Ω _ H

theorem wick_covariant_source_density_poincare (a : Parameters) (s : ℝ)
    (q : ProperPoincareTransform) (Ω : Opens CoordinatePoint)
    (r : Quotient wickCovariantRaySetoid) :
    wickRoleQg a s (wickAffineMetricRegion q.left.toAdd q.right Ω)
      (wickCovariantSourceIndex a s (wickAffineMetricRegion q.left.toAdd q.right Ω)
        (wickCovariantPoincareRay a q r)) =
      representedMetricSource ((originalWickRayMetricResponse a s Ω (wickCovariantOriginalRay a r)).comp
        (wickNativeAffineMetricInverseCLM q.left.toAdd q.right Ω)) := by
  rw [wick_covariant_source_prequotient_square,wick_covariant_original_ray_poincare]
  exact wick_role_concrete_source_poincare a s Ω (wickCovariantOriginalRay a r) q.left.toAdd q.right

end AASCKleinGordon
