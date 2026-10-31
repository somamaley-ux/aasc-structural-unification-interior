import KGNRFreeSSQ1
import UnitaryExactGeneratorConverse

/-! Exact generator domain for the already constructed free flow; uniqueness
only against another exact generator of this same phase-fixed group. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon

theorem kg_nr_spatial_flow_inverse (a : Parameters) (t : ℝ) (f : KGNRSpatialHilbert) :
    (kgNRSpatialFreeFlow a t).symm f = kgNRSpatialFreeFlow a (-t) f := by
  apply (kgNRSpatialFreeFlow a t).injective
  rw [(kgNRSpatialFreeFlow a t).apply_symm_apply,← kg_nr_spatial_group_add,
    add_neg_cancel,kg_nr_spatial_group_zero]

theorem kg_nr_spatial_exact_generator (a : Parameters) :
    GlobalCharge.ExactGenerator (Translation.coefficient a.hbar)
      (kgNRSpatialFreeFlow a) (kgNRSpatialKinetic a) := by
  constructor
  · intro f
    constructor
    · exact GlobalCharge.differentiable_orbit_mem_selfAdjoint_domain
        (Translation.coefficient a.hbar)
        (GlobalCharge.physical_generator_coefficient_nonzero a.hbar a.hbar_pos)
        (by simp [Translation.coefficient,neg_div])
        (kgNRSpatialFreeFlow a) (kg_nr_spatial_group_zero a)
        (kg_nr_spatial_flow_inverse a) (kgNRSpatialKinetic a)
        (kg_nr_spatial_kinetic_self_adjoint a) (kg_nr_spatial_free_flow_generator a) f
    · intro hf
      exact (kg_nr_spatial_free_flow_generator a ⟨f,hf⟩).differentiableAt
  · exact kg_nr_spatial_free_flow_generator a

theorem kg_nr_same_flow_exact_generator_unique (a : Parameters)
    (H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert)
    (hH : GlobalCharge.ExactGenerator (Translation.coefficient a.hbar)
      (kgNRSpatialFreeFlow a) H) : H = kgNRSpatialKinetic a :=
  GlobalCharge.exact_unbounded_generator_unique (Translation.coefficient a.hbar)
    (GlobalCharge.physical_generator_coefficient_nonzero a.hbar a.hbar_pos)
    _ _ H _ hH (kg_nr_spatial_exact_generator a) (fun _ _ => rfl)

end AASCKleinGordon
