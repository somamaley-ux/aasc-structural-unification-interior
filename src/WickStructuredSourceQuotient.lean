import WickRoleRayDescent

noncomputable section
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

/-- Actual statuses of this fixed smooth, closed, boundaryless envelope.
These are data in the source relation; proofs live in the actual tensor ledger. -/
abbrev WickSourceLedgerValue (Ω : Opens CoordinatePoint) :=
  Set CoordinatePoint × (CoordinateVectorProbe Ω →L[ℝ] ℝ) × ℕ∞ × Set CoordinatePoint

def wickOriginalSourceLedgerValue (Ω : Opens CoordinatePoint) : WickSourceLedgerValue Ω :=
  (wickOriginalClosedSupportEnvelope,0,⊤,∅)

/-- The A02 triple on the explicitly declared original action/predictive
branch. Its attachment is constructed below, not postulated as an input. -/
structure WickRoleSourcePresentation (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) where
  response : WickNonzeroCore
  attachment : WickNativeDeclaredSourcePresentation a s
    (originalWickUnitRepresentative a response.val) Ω (wickOriginalMetricNeighborhood Ω)
  ledger : WickSourceLedgerValue Ω
  ledger_exact : ledger=wickOriginalSourceLedgerValue Ω

def wickOriginalRoleSource (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (u : WickNonzeroCore) : WickRoleSourcePresentation a s Ω where
  response := u
  attachment := wickOriginalNativeSourcePresentation a s (originalWickUnitRepresentative a u.val) Ω
  ledger := wickOriginalSourceLedgerValue Ω
  ledger_exact := rfl

def wickRoleSourceMetResp {a : Parameters} {s : ℝ} {Ω : Opens CoordinatePoint}
    (p : WickRoleSourcePresentation a s Ω) (H : MetricSourceProbe Ω) (z : ℝ) : Prop :=
  ∃ π,wickKGOriginalMetInc H π ∧ p.attachment.entire_readout π=.first z

/-- All four A02 source-equivalence clauses are retained. In particular
the full original base relation is not replaced by witness equality. -/
def WickRoleSourceEquivalent {a : Parameters} {s : ℝ} {Ω : Opens CoordinatePoint}
    (p q : WickRoleSourcePresentation a s Ω) : Prop :=
  (wickOriginalRoleSetoid a s Ω).r p.response q.response ∧
  (∀ H z,wickRoleSourceMetResp p H z ↔ wickRoleSourceMetResp q H z) ∧
  p.attachment.functional=q.attachment.functional ∧
  p.attachment.represented=q.attachment.represented ∧ p.ledger=q.ledger

theorem wick_full_role_implies_source_agreement {a : Parameters} {s : ℝ}
    {Ω : Opens CoordinatePoint} (p q : WickRoleSourcePresentation a s Ω)
    (same : (wickOriginalRoleSetoid a s Ω).r p.response q.response) :
    WickRoleSourceEquivalent p q := by
  have functionals : p.attachment.functional=q.attachment.functional := by
    rw [p.attachment.same_original_source,q.attachment.same_original_source]
    ext H
    have readout := wick_role_equivalence_entire_metric a s Ω p.response q.response same
      (.first (wickKGIdentityAct H))
    have first := WickKGOriginalReadout.first.inj readout
    simpa only [wick_KG_original_first_output_computed,wick_KG_identity_tangent] using first
  refine ⟨same,?_,functionals,?_,p.ledger_exact.trans q.ledger_exact.symm⟩
  · intro H z
    rw [show wickRoleSourceMetResp p H z ↔ p.attachment.functional H=z from p.attachment.source_graph H z,
      show wickRoleSourceMetResp q H z ↔ q.attachment.functional H=z from q.attachment.source_graph H z,
      functionals]
  · apply q.attachment.representation_unique
    intro H
    exact (p.attachment.half_pairing H).trans (DFunLike.congr_fun functionals H)

def wickRoleSourceSetoid (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    Setoid (WickRoleSourcePresentation a s Ω) where
  r := WickRoleSourceEquivalent
  iseqv := ⟨fun p => wick_full_role_implies_source_agreement p p (fun _ => rfl),
    fun h => wick_full_role_implies_source_agreement _ _ (fun π => (h.1 π).symm),
    fun h k => wick_full_role_implies_source_agreement _ _ (fun π => (h.1 π).trans (k.1 π))⟩

abbrev WickRoleQsrc (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :=
  Quotient (wickRoleSourceSetoid a s Ω)

def wickRolePiA (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (p : WickRoleSourcePresentation a s Ω) : WickRoleQsrc a s Ω := Quotient.mk _ p

def wickRoleForget (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    WickRoleQsrc a s Ω → WickRoleQresp a s Ω :=
  Quotient.map WickRoleSourcePresentation.response (fun _ _ same => same.1)

def wickRoleQsrcbase (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    Set (WickRoleQresp a s Ω) := Set.range (wickRoleForget a s Ω)

def wickRoleF (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (q : WickRoleQsrc a s Ω) : wickRoleQsrcbase a s Ω := ⟨wickRoleForget a s Ω q,⟨q,rfl⟩⟩

theorem wick_role_F_surjective (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    Function.Surjective (wickRoleF a s Ω) := by
  rintro ⟨q,src,hsrc⟩
  exact ⟨src,Subtype.ext hsrc⟩

/-- Concrete representative exists before quotienting. -/
def wickRoleTA {a : Parameters} {s : ℝ} {Ω : Opens CoordinatePoint}
    (p : WickRoleSourcePresentation a s Ω) : SymmetricSourceComponents Ω := p.attachment.represented

/-- Fixed-chart density representative. Cross-chart naturality is proved
separately; this is not a quotient by arbitrary diffeomorphisms/improvements. -/
def wickRoleQg (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    WickRoleQsrc a s Ω → SymmetricSourceComponents Ω :=
  Quotient.lift wickRoleTA (fun _ _ same => same.2.2.2.1)

def wickRoleSx (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (ray : Quotient wickCoreRaySetoid) : WickRoleSourcePresentation a s Ω :=
  wickOriginalRoleSource a s Ω ray.out

theorem wick_role_source_base_square (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (ray : Quotient wickCoreRaySetoid) :
    (wickRoleF a s Ω (wickRolePiA a s Ω (wickRoleSx a s Ω ray))).val=
      wickOriginalRoleEval a s Ω ray :=
  congrArg (wickOriginalRoleEval a s Ω) (Quotient.out_eq ray)

theorem wick_role_concrete_density_square (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (ray : Quotient wickCoreRaySetoid) :
    wickRoleQg a s Ω (wickRolePiA a s Ω (wickRoleSx a s Ω ray))=
      wickRoleTA (wickRoleSx a s Ω ray) := rfl

theorem wick_role_source_full_signature_preserved (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (p q : WickRoleSourcePresentation a s Ω)
    (same : wickRolePiA a s Ω p=wickRolePiA a s Ω q) :
    (∀ π,wickOriginalRoleOutput a s Ω p.response π=wickOriginalRoleOutput a s Ω q.response π) ∧
      p.ledger=q.ledger := by
  have h := Quotient.exact same
  exact ⟨h.1,h.2.2.2.2⟩

end AASCKleinGordon
