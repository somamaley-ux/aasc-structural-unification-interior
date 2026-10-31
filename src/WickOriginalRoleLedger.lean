import WickOriginalMetricProjection
import KGGeneralPoincareRepresentation

noncomputable section
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

/-- Complete protocol type of the declared action-plus-predictive-comparison
KG branch. This does not identify an arbitrary richer original ledger. -/
inductive WickRoleProtocol (Ω : Opens CoordinatePoint) where
  | metric (act : WickKGOriginalProtocol Ω)
  | comparison (g : ProperPoincareTransform) (probe : WickNonzeroCore)

inductive WickRoleReadout where
  | metric (value : WickKGOriginalReadout)
  | probability (value : ℝ)

/-- A comparison is an actual normalized core-probe transition probability
in the original Hilbert carrier, not a prospective source readout. -/
def wickOriginalRoleComparison (a : Parameters) (u v : WickNonzeroCore)
    (g : ProperPoincareTransform) : ℝ :=
  ‖inner ℂ (finiteParticleCoreToFock a (originalWickUnitRepresentative a v.val))
    (originalFockPoincareRepresentation a g
      (finiteParticleCoreToFock a (originalWickUnitRepresentative a u.val)))‖^2

def wickOriginalRoleOutput (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (u : WickNonzeroCore) : WickRoleProtocol Ω → WickRoleReadout
  | .metric π => .metric (wickKGOriginalOutput a s (originalWickUnitRepresentative a u.val) π)
  | .comparison g v => .probability (wickOriginalRoleComparison a u v g)

def wickOriginalRoleSetoid (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    Setoid WickNonzeroCore where
  r u v := ∀ π,wickOriginalRoleOutput a s Ω u π=wickOriginalRoleOutput a s Ω v π
  iseqv := ⟨fun _ _ => rfl,fun h π => (h π).symm,fun h k π => (h π).trans (k π)⟩

abbrev WickRoleQresp (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :=
  Quotient (wickOriginalRoleSetoid a s Ω)

def wickRoleClassify (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (u : WickNonzeroCore) : WickRoleQresp a s Ω := Quotient.mk _ u

theorem wick_role_equivalence_entire_metric (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u v : WickNonzeroCore)
    (same : (wickOriginalRoleSetoid a s Ω).r u v) (π : WickKGOriginalProtocol Ω) :
    wickKGOriginalOutput a s (originalWickUnitRepresentative a u.val) π=
      wickKGOriginalOutput a s (originalWickUnitRepresentative a v.val) π :=
  WickRoleReadout.metric.inj (same (.metric π))

theorem wick_role_equivalence_transport_comparisons (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (u v : WickNonzeroCore)
    (same : (wickOriginalRoleSetoid a s Ω).r u v)
    (g : ProperPoincareTransform) (probe : WickNonzeroCore) :
    wickOriginalRoleComparison a u probe g=wickOriginalRoleComparison a v probe g :=
  WickRoleReadout.probability.inj (same (.comparison g probe))

end AASCKleinGordon
