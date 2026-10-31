import KGQuantumOrbitDescent
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Maps.OpenQuotient
import Mathlib.Topology.Constructions.SumProd

/-! Joint tensor and probability continuity uses an OPEN orbit quotient.
Separate quotient descent alone is not used to infer joint continuity. -/
noncomputable section
namespace AASCKleinGordon
open KGQuantum
open scoped TensorProduct
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

def kgTensorCLM : E →L[ℂ] F →L[ℂ] E ⊗[ℂ] F :=
  (TensorProduct.mk ℂ E F).mkContinuous₂ 1 (by
    intro x y
    change ‖x ⊗ₜ[ℂ] y‖ ≤ 1 * ‖x‖ * ‖y‖
    rw [TensorProduct.norm_tmul,one_mul])

theorem kg_raw_tensor_joint_continuous :
    Continuous (fun p : PureVector E × PureVector F => kgRawTensor p.1 p.2) := by
  have h : Continuous (fun p : PureVector E × PureVector F =>
      kgTensorCLM (E := E) (F := F) p.1.val p.2.val) :=
    ((kgTensorCLM (E := E) (F := F)).continuous.comp
      (continuous_subtype_val.comp continuous_fst)).clm_apply
        (continuous_subtype_val.comp continuous_snd)
  exact h.subtype_mk _

theorem kg_scalar_representative_continuous (c : ℂˣ) :
    Continuous (PureVector.smul (c : ℂ) c.ne_zero : PureVector E → PureVector E) :=
  (continuous_const.smul continuous_subtype_val).subtype_mk _

theorem kg_scalar_saturation (U : Set (PureVector E)) :
    (rayMap E) ⁻¹' ((rayMap E) '' U)=
      ⋃ c : ℂˣ,(PureVector.smul (c : ℂ) c.ne_zero) ⁻¹' U := by
  ext x
  constructor
  · rintro ⟨u,hu,hq⟩
    obtain ⟨c,hc,h⟩ := (rayMap_eq_iff E u x).mp hq
    apply Set.mem_iUnion.mpr
    refine ⟨(Units.mk0 c hc)⁻¹,?_⟩
    have back : PureVector.smul c⁻¹ (inv_ne_zero hc) x=u := by
      apply Subtype.ext
      change c⁻¹ • x.val=u.val
      rw [← h,smul_smul,inv_mul_cancel₀ hc,one_smul]
    change PureVector.smul c⁻¹ _ x ∈ U
    rw [back]
    exact hu
  · intro h
    obtain ⟨c,hc⟩ := Set.mem_iUnion.mp h
    exact ⟨PureVector.smul (c : ℂ) c.ne_zero x,hc,rayMap_smul E (c : ℂ) c.ne_zero x⟩

theorem kg_ray_isOpenMap : IsOpenMap (rayMap E) := by
  intro U hU
  change IsOpen ((rayMap E) ⁻¹' ((rayMap E) '' U))
  rw [kg_scalar_saturation]
  exact isOpen_iUnion (fun c => hU.preimage (kg_scalar_representative_continuous c))

theorem kg_ray_open_quotient : IsOpenQuotientMap (rayMap E) := by
  refine ⟨?_,kg_raw_orbit_map_continuous,kg_ray_isOpenMap⟩
  intro r
  induction r using Quotient.inductionOn with | _ x => exact ⟨x,rfl⟩

theorem kg_tensor_ray_joint_continuous :
    Continuous (fun p : PhysicalRay E × PhysicalRay F => kgTensorRay p.1 p.2) := by
  apply ((kg_ray_open_quotient (E := E)).prodMap
    (kg_ray_open_quotient (E := F))).continuous_comp_iff.mp
  change Continuous (fun p : PureVector E × PureVector F => rayMap _ (kgRawTensor p.1 p.2))
  exact kg_raw_orbit_map_continuous.comp kg_raw_tensor_joint_continuous

theorem kg_ray_probability_joint_continuous :
    Continuous (fun p : PhysicalRay E × PhysicalRay E => rayTransitionProbability p.1 p.2) := by
  apply ((kg_ray_open_quotient (E := E)).prodMap
    (kg_ray_open_quotient (E := E))).continuous_comp_iff.mp
  exact kg_raw_probability_continuous

end AASCKleinGordon
