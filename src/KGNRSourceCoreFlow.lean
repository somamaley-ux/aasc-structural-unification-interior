import KGNRSourceKineticCore

/-! Construct the NR phase on the actual unchanged Schwartz source core, then
prove its intertwining with the full spatial limiting flow. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory
open Filter
open scoped SchwartzMap Topology
namespace AASCKleinGordon
attribute [local irreducible] kgIsolatedMomentumUnitary kgWeightedMomentumUnitary
  kgPhysicalSpatialUnitary kgOriginalSpatialCoreEquiv

theorem kg_nr_spatial_core_equiv_value (a : Parameters) (x : kgOriginalOneCore a) :
    (kgOriginalSpatialCoreEquiv a x).val = kgOriginalOneCoreSpatialEmbedding a x := by
  unfold kgOriginalSpatialCoreEquiv
  rfl

theorem kg_nr_spatial_core_inverse_value (a : Parameters) (x : kgOriginalSpatialCore a) :
    kgOriginalOneCoreSpatialEmbedding a ((kgOriginalSpatialCoreEquiv a).symm x) = x.val :=
  (kg_nr_spatial_core_equiv_value a ((kgOriginalSpatialCoreEquiv a).symm x)).symm.trans
    (congrArg (fun z : kgOriginalSpatialCore a => z.val)
      ((kgOriginalSpatialCoreEquiv a).apply_symm_apply x))

theorem kg_nr_phase_temperate (a : Parameters) (t : ℝ) :
    (fun p => Translation.phase a.hbar t (kgNRKineticEnergy a p)).HasTemperateGrowth :=
  (translationPhase_temperate a.hbar t).comp (kg_nr_kinetic_temperate a)

def kgNRSchwartzFlow (a : Parameters) (t : ℝ) : 𝓢(Momentum,ℂ) →L[ℂ] 𝓢(Momentum,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun p => Translation.phase a.hbar t (kgNRKineticEnergy a p))

theorem kg_nr_schwartz_flow_apply (a : Parameters) (t : ℝ)
    (f : 𝓢(Momentum,ℂ)) (p : Momentum) :
    kgNRSchwartzFlow a t f p = Translation.phase a.hbar t (kgNRKineticEnergy a p)*f p :=
  SchwartzMap.smulLeftCLM_apply_apply (kg_nr_phase_temperate a t) f p

theorem kg_nr_schwartz_flow_zero (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    kgNRSchwartzFlow a 0 f = f := by
  ext p
  simp only [kg_nr_schwartz_flow_apply,Translation.phase_zero,one_mul]

theorem kg_nr_schwartz_flow_add (a : Parameters) (t s : ℝ) (f : 𝓢(Momentum,ℂ)) :
    kgNRSchwartzFlow a (t+s) f = kgNRSchwartzFlow a t (kgNRSchwartzFlow a s f) := by
  ext p
  simp only [kg_nr_schwartz_flow_apply,Translation.phase_add,mul_assoc]

def kgNROriginalCoreFlowLinear (a : Parameters) (t : ℝ) :
    kgOriginalOneCore a →ₗ[ℂ] kgOriginalOneCore a :=
  ((kgOriginalOneCoreSchwartzEquiv a).toLinearMap.comp
    (kgNRSchwartzFlow a t).toLinearMap).comp (kgOriginalOneCoreSchwartzEquiv a).symm.toLinearMap

theorem kg_nr_weighted_schwartz_phase_square (a : Parameters) (t : ℝ)
    (f : 𝓢(Momentum,ℂ)) :
    kgWeightedMomentumUnitary a (oneParticleSchwartzToHilbert a (kgNRSchwartzFlow a t f)) =
      kgNRFreeMomentumFlow a t (kgWeightedMomentumUnitary a (oneParticleSchwartzToHilbert a f)) := by
  apply Lp.ext
  filter_upwards [kg_nr_weighted_unitary_ae a (oneParticleSchwartzToHilbert a f),
    kg_nr_weighted_unitary_ae a (oneParticleSchwartzToHilbert a (kgNRSchwartzFlow a t f)),
    (kg_wigner_ae a).mp (f.coeFn_toLp 2 (wignerMeasure a)),
    (kg_wigner_ae a).mp ((kgNRSchwartzFlow a t f).coeFn_toLp 2 (wignerMeasure a)),
    Multiplication.phaseMultiplier_ae (kgNRKineticEnergy a) (kg_nr_kinetic_measurable a)
      a.hbar t (kgWeightedMomentumUnitary a (oneParticleSchwartzToHilbert a f))]
    with p hf hg hs ht hu
  change kgWeightedMomentumUnitary a (oneParticleSchwartzToHilbert a (kgNRSchwartzFlow a t f)) p =
    Multiplication.phaseMultiplier (kgNRKineticEnergy a) (kg_nr_kinetic_measurable a)
      a.hbar t (kgWeightedMomentumUnitary a (oneParticleSchwartzToHilbert a f)) p
  change (oneParticleSchwartzToHilbert a f) p = f p at hs
  change (oneParticleSchwartzToHilbert a (kgNRSchwartzFlow a t f)) p = kgNRSchwartzFlow a t f p at ht
  rw [hg,ht,kg_nr_schwartz_flow_apply,hu]
  change _ = Translation.phase a.hbar t (kgNRKineticEnergy a p)*
    kgWeightedMomentumUnitary a (oneParticleSchwartzToHilbert a f) p
  rw [hf,hs]
  ring

theorem kg_nr_original_core_flow_momentum_square (a : Parameters) (t : ℝ)
    (x : kgOriginalOneCore a) :
    kgIsolatedMomentumUnitary a
      (kgOriginalOneCoreToIsolated a (kgNROriginalCoreFlowLinear a t x)) =
      kgNRFreeMomentumFlow a t
        (kgIsolatedMomentumUnitary a (kgOriginalOneCoreToIsolated a x)) := by
  have hc : kgOriginalOneCoreCoordinates a (kgNROriginalCoreFlowLinear a t x) =
      kgNRSchwartzFlow a t (kgOriginalOneCoreCoordinates a x) :=
    kg_original_one_core_coordinates_of_schwartz a _
  have hl := (kg_original_one_core_momentum_coordinates a (kgNROriginalCoreFlowLinear a t x)).trans
    (congrArg (fun f : 𝓢(Momentum,ℂ) => kgWeightedMomentumUnitary a
      (oneParticleSchwartzToHilbert a f)) hc)
  exact hl.trans ((kg_nr_weighted_schwartz_phase_square a t _).trans
    (congrArg (kgNRFreeMomentumFlow a t) (kg_original_one_core_momentum_coordinates a x).symm))

theorem kg_nr_original_core_flow_norm (a : Parameters) (t : ℝ)
    (x : kgOriginalOneCore a) : ‖kgNROriginalCoreFlowLinear a t x‖ = ‖x‖ := by
  let L := (kgIsolatedMomentumUnitary a).toLinearIsometry.comp (kgOriginalOneCoreToIsolated a)
  calc
    _ = ‖L (kgNROriginalCoreFlowLinear a t x)‖ := (L.norm_map _).symm
    _ = ‖kgNRFreeMomentumFlow a t (L x)‖ :=
      congrArg norm (kg_nr_original_core_flow_momentum_square a t x)
    _ = ‖x‖ := ((kgNRFreeMomentumFlow a t).norm_map (L x)).trans (L.norm_map x)

def kgNROriginalOneCoreFlow (a : Parameters) (t : ℝ) :
    kgOriginalOneCore a ≃ₗᵢ[ℂ] kgOriginalOneCore a where
  toFun := kgNROriginalCoreFlowLinear a t
  invFun := kgNROriginalCoreFlowLinear a (-t)
  left_inv x := by
    apply kg_original_one_core_coordinates_injective a
    change kgOriginalOneCoreCoordinates a (kgOriginalOneCoreOfSchwartz a
      (kgNRSchwartzFlow a (-t) (kgOriginalOneCoreCoordinates a
        (kgOriginalOneCoreOfSchwartz a (kgNRSchwartzFlow a t (kgOriginalOneCoreCoordinates a x)))))) = _
    rw [kg_original_one_core_coordinates_of_schwartz,
      kg_original_one_core_coordinates_of_schwartz,← kg_nr_schwartz_flow_add,
      neg_add_cancel,kg_nr_schwartz_flow_zero]
  right_inv x := by
    apply kg_original_one_core_coordinates_injective a
    change kgOriginalOneCoreCoordinates a (kgOriginalOneCoreOfSchwartz a
      (kgNRSchwartzFlow a t (kgOriginalOneCoreCoordinates a
        (kgOriginalOneCoreOfSchwartz a (kgNRSchwartzFlow a (-t) (kgOriginalOneCoreCoordinates a x)))))) = _
    rw [kg_original_one_core_coordinates_of_schwartz,
      kg_original_one_core_coordinates_of_schwartz,← kg_nr_schwartz_flow_add,
      add_neg_cancel,kg_nr_schwartz_flow_zero]
  map_add' := (kgNROriginalCoreFlowLinear a t).map_add
  map_smul' := (kgNROriginalCoreFlowLinear a t).map_smul
  norm_map' := kg_nr_original_core_flow_norm a t

def kgNRSpatialCoreFlow (a : Parameters) (t : ℝ) :
    kgOriginalSpatialCore a ≃ₗᵢ[ℂ] kgOriginalSpatialCore a :=
  (((kgOriginalSpatialCoreEquiv a).symm).trans (kgNROriginalOneCoreFlow a t)).trans
    (kgOriginalSpatialCoreEquiv a)

theorem kg_nr_original_one_core_flow_zero (a : Parameters) (x : kgOriginalOneCore a) :
    kgNROriginalOneCoreFlow a 0 x = x := by
  apply (kgOriginalOneCoreToIsolated a).injective
  apply (kgIsolatedMomentumUnitary a).injective
  change kgIsolatedMomentumUnitary a
    (kgOriginalOneCoreToIsolated a (kgNROriginalCoreFlowLinear a 0 x)) =
    kgIsolatedMomentumUnitary a (kgOriginalOneCoreToIsolated a x)
  exact (kg_nr_original_core_flow_momentum_square a 0 x).trans
    (Multiplication.phaseMultiplier_zero (kgNRKineticEnergy a) (kg_nr_kinetic_measurable a)
      a.hbar (kgIsolatedMomentumUnitary a (kgOriginalOneCoreToIsolated a x)))

theorem kg_nr_original_one_core_flow_add (a : Parameters) (t s : ℝ)
    (x : kgOriginalOneCore a) :
    kgNROriginalOneCoreFlow a (t+s) x =
      kgNROriginalOneCoreFlow a t (kgNROriginalOneCoreFlow a s x) := by
  apply (kgOriginalOneCoreToIsolated a).injective
  apply (kgIsolatedMomentumUnitary a).injective
  change kgIsolatedMomentumUnitary a
    (kgOriginalOneCoreToIsolated a (kgNROriginalCoreFlowLinear a (t+s) x)) =
    kgIsolatedMomentumUnitary a (kgOriginalOneCoreToIsolated a
      (kgNROriginalCoreFlowLinear a t (kgNROriginalCoreFlowLinear a s x)))
  exact (kg_nr_original_core_flow_momentum_square a (t+s) x).trans
    ((kg_nr_free_momentum_flow_add a t s _).trans
      ((congrArg (kgNRFreeMomentumFlow a t)
        (kg_nr_original_core_flow_momentum_square a s x).symm).trans
          (kg_nr_original_core_flow_momentum_square a t (kgNROriginalCoreFlowLinear a s x)).symm))

theorem kg_nr_spatial_core_flow_zero (a : Parameters) (x : kgOriginalSpatialCore a) :
    kgNRSpatialCoreFlow a 0 x = x := by
  change kgOriginalSpatialCoreEquiv a
    (kgNROriginalOneCoreFlow a 0 ((kgOriginalSpatialCoreEquiv a).symm x)) = x
  exact (congrArg (kgOriginalSpatialCoreEquiv a)
    (kg_nr_original_one_core_flow_zero a ((kgOriginalSpatialCoreEquiv a).symm x))).trans
      ((kgOriginalSpatialCoreEquiv a).apply_symm_apply x)

theorem kg_nr_spatial_core_flow_add (a : Parameters) (t s : ℝ)
    (x : kgOriginalSpatialCore a) :
    kgNRSpatialCoreFlow a (t+s) x = kgNRSpatialCoreFlow a t (kgNRSpatialCoreFlow a s x) := by
  change kgOriginalSpatialCoreEquiv a
    (kgNROriginalOneCoreFlow a (t+s) ((kgOriginalSpatialCoreEquiv a).symm x)) =
    kgOriginalSpatialCoreEquiv a (kgNROriginalOneCoreFlow a t
      ((kgOriginalSpatialCoreEquiv a).symm (kgOriginalSpatialCoreEquiv a
        (kgNROriginalOneCoreFlow a s ((kgOriginalSpatialCoreEquiv a).symm x)))))
  exact (congrArg (kgOriginalSpatialCoreEquiv a)
    (kg_nr_original_one_core_flow_add a t s ((kgOriginalSpatialCoreEquiv a).symm x))).trans
      (congrArg (fun y : kgOriginalOneCore a => kgOriginalSpatialCoreEquiv a
        (kgNROriginalOneCoreFlow a t y))
          ((kgOriginalSpatialCoreEquiv a).symm_apply_apply
            (kgNROriginalOneCoreFlow a s ((kgOriginalSpatialCoreEquiv a).symm x)))).symm

theorem kg_nr_original_source_phase_spatial_square (a : Parameters) (t : ℝ)
    (x : kgOriginalOneCore a) :
    kgOriginalOneCoreSpatialEmbedding a (kgNROriginalOneCoreFlow a t x) =
      kgNRSpatialFreeFlow a t (kgOriginalOneCoreSpatialEmbedding a x) := by
  have hp := (congrArg (kgPhysicalSpatialUnitary a).symm
    (kg_original_one_core_spatial_formula a x)).trans
      ((kgPhysicalSpatialUnitary a).symm_apply_apply _)
  exact (kg_original_one_core_spatial_formula a (kgNROriginalCoreFlowLinear a t x)).trans
    ((congrArg (kgPhysicalSpatialUnitary a)
      (kg_nr_original_core_flow_momentum_square a t x)).trans
        (congrArg (fun f => kgPhysicalSpatialUnitary a (kgNRFreeMomentumFlow a t f)) hp).symm)

theorem kg_nr_spatial_core_flow_original_value (a : Parameters) (t : ℝ)
    (x : kgOriginalOneCore a) :
    (kgNRSpatialCoreFlow a t (kgOriginalSpatialCoreEquiv a x)).val =
      kgNRSpatialFreeFlow a t (kgOriginalOneCoreSpatialEmbedding a x) := by
  change (kgOriginalSpatialCoreEquiv a
    (kgNROriginalOneCoreFlow a t
      ((kgOriginalSpatialCoreEquiv a).symm (kgOriginalSpatialCoreEquiv a x)))).val = _
  exact (congrArg (fun y : kgOriginalOneCore a =>
    (kgOriginalSpatialCoreEquiv a (kgNROriginalOneCoreFlow a t y)).val)
      ((kgOriginalSpatialCoreEquiv a).symm_apply_apply x)).trans
        ((kg_nr_spatial_core_equiv_value a (kgNROriginalOneCoreFlow a t x)).trans
          (kg_nr_original_source_phase_spatial_square a t x))

theorem kg_nr_spatial_core_flow_full_value (a : Parameters) (t : ℝ)
    (x : kgOriginalSpatialCore a) :
    (kgNRSpatialCoreFlow a t x).val = kgNRSpatialFreeFlow a t x.val := by
  have h := kg_nr_spatial_core_flow_original_value a t ((kgOriginalSpatialCoreEquiv a).symm x)
  have hl := congrArg (fun y : kgOriginalSpatialCore a => (kgNRSpatialCoreFlow a t y).val)
    ((kgOriginalSpatialCoreEquiv a).apply_symm_apply x)
  exact hl.symm.trans (h.trans
    (congrArg (kgNRSpatialFreeFlow a t) (kg_nr_spatial_core_inverse_value a x)))

theorem kg_nr_full_flow_preserves_original_spatial_core (a : Parameters) (t : ℝ)
    (x : kgOriginalSpatialCore a) : kgNRSpatialFreeFlow a t x.val ∈ kgOriginalSpatialCore a := by
  rw [← kg_nr_spatial_core_flow_full_value]
  exact (kgNRSpatialCoreFlow a t x).prop

theorem kg_nr_source_phase_is_original_rest_limit (a : Parameters) (t : ℝ)
    (x : kgOriginalOneCore a) :
    Tendsto (fun c : ℝ => kgOriginalRestSpatialFlow a c t
      (kgOriginalOneCoreSpatialEmbedding a x)) atTop
      (nhds (kgOriginalOneCoreSpatialEmbedding a (kgNROriginalOneCoreFlow a t x))) := by
  rw [kg_nr_original_source_phase_spatial_square]
  exact kg_original_rest_spatial_strong_nr_limit a t _

theorem kg_nr_source_core_spatial_derivative (a : Parameters) (x : kgOriginalSpatialCore a) :
    HasDerivAt (fun t => (kgNRSpatialCoreFlow a t x).val)
      (Translation.coefficient a.hbar • kgNRSpatialKinetic a
        ⟨x.val,kg_original_spatial_core_mem_maximal_kinetic_domain a x⟩) 0 := by
  simpa only [kg_nr_spatial_core_flow_full_value] using
    kg_nr_spatial_free_flow_generator a
      ⟨x.val,kg_original_spatial_core_mem_maximal_kinetic_domain a x⟩

theorem kg_nr_source_core_flow_continuous (a : Parameters) (x : kgOriginalSpatialCore a) :
    Continuous (fun t => kgNRSpatialCoreFlow a t x) := by
  have hc : Continuous (fun t => kgNRSpatialFreeFlow a t x.val) :=
    (kgPhysicalSpatialUnitary a).continuous.comp
      (kg_nr_free_momentum_flow_continuous a ((kgPhysicalSpatialUnitary a).symm x.val))
  have he : (fun t => kgNRSpatialCoreFlow a t x) =
      (fun t => (⟨kgNRSpatialFreeFlow a t x.val,
        kg_nr_full_flow_preserves_original_spatial_core a t x⟩ : kgOriginalSpatialCore a)) := by
    funext t
    exact Subtype.ext (kg_nr_spatial_core_flow_full_value a t x)
  rw [he]
  exact hc.subtype_mk _

end AASCKleinGordon
