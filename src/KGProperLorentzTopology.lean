import KGGeneralLorentzSchwartz
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Analysis.Normed.Operator.Banach

/-! The original Lorentz subgroup carries the topology induced by its actual
continuous-linear units. This is the finite-dimensional GL topology, including
forward and inverse operator-norm convergence; no discrete topology is used. -/
noncomputable section
open scoped Topology
namespace AASCKleinGordon

def properLorentzUnit (L : ProperLorentzTransform) : (FourMomentum →L[ℝ] FourMomentum)ˣ :=
  (properLorentzFourCLE L).toUnit

instance properLorentzTopologicalSpace : TopologicalSpace ProperLorentzTransform :=
  TopologicalSpace.induced properLorentzUnit inferInstance

theorem properLorentzUnit_isInducing : Topology.IsInducing properLorentzUnit := ⟨rfl⟩

theorem properLorentzUnit_injective : Function.Injective properLorentzUnit := by
  intro L M h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  exact congrArg (fun u : (FourMomentum →L[ℝ] FourMomentum)ˣ => (u : FourMomentum →L[ℝ] FourMomentum) v) h

theorem properLorentzUnit_isEmbedding : Topology.IsEmbedding properLorentzUnit :=
  ⟨properLorentzUnit_isInducing,properLorentzUnit_injective⟩

instance properLorentzFirstCountable : FirstCountableTopology ProperLorentzTransform := by
  letI : FirstCountableTopology (FourMomentum →L[ℝ] FourMomentum)ˣ :=
    Units.isInducing_embedProduct.firstCountableTopology
  exact properLorentzUnit_isInducing.firstCountableTopology

theorem properLorentzUnit_continuous : Continuous properLorentzUnit := continuous_induced_dom

theorem properLorentz_forward_continuous :
    Continuous (fun L : ProperLorentzTransform => (properLorentzFourCLE L).toContinuousLinearMap) :=
  Units.continuous_val.comp properLorentzUnit_continuous

theorem properLorentz_inverse_continuous :
    Continuous (fun L : ProperLorentzTransform => (properLorentzFourCLE L⁻¹).toContinuousLinearMap) :=
  Units.continuous_coe_inv.comp properLorentzUnit_continuous

instance properLorentzTopologicalGroup : IsTopologicalGroup ProperLorentzTransform where
  continuous_mul := by
    apply properLorentzUnit_isInducing.continuous_iff.mpr
    exact (properLorentzUnit_continuous.comp continuous_fst).mul
      (properLorentzUnit_continuous.comp continuous_snd)
  continuous_inv := by
    apply properLorentzUnit_isInducing.continuous_iff.mpr
    exact properLorentzUnit_continuous.inv

theorem properLorentz_continuous_iff {X : Type*} [TopologicalSpace X]
    (f : X → ProperLorentzTransform) : Continuous f ↔
      Continuous (fun x => (properLorentzFourCLE (f x)).toContinuousLinearMap) ∧
      Continuous (fun x => (properLorentzFourCLE (f x)⁻¹).toContinuousLinearMap) := by
  rw [properLorentzUnit_isInducing.continuous_iff,Units.continuous_iff]
  rfl

theorem properLorentz_evaluation_continuous (v : FourMomentum) :
    Continuous (fun L : ProperLorentzTransform => L.val v) :=
  properLorentz_forward_continuous.clm_apply continuous_const

theorem lorentzShellMap_parameter_continuous (a : Parameters) (p : Momentum) :
    Continuous (fun L : ProperLorentzTransform => lorentzShellMap a L p) := by
  change Continuous (fun L => fourSpatialProjection (properLorentzFourCLE L (massShell a p)))
  exact fourSpatialProjection.continuous.comp (properLorentz_evaluation_continuous _)

end AASCKleinGordon
