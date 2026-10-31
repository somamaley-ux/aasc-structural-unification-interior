import KGFamilyStandingDescent

/-! Nondegeneracy uses a nonzero orthogonal preparation and nonzero test.
The failed execution remains distinct from its successful ledger report. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 CategoryTheory TopologicalSpace AASCSemanticExhaustion
open scoped TensorProduct
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

section GenericFailure
variable {E F Y : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem kg_inner_zero_of_probability_zero (x y : PureVector E)
    (h : transitionProbability x y=0) : inner ℂ x.val y.val=0 := by
  have numerator : ‖inner ℂ x.val y.val‖ ^ 2=0 :=
    (div_eq_zero_iff.mp h).resolve_right (transitionProbability_denominator_ne_zero x y)
  exact norm_eq_zero.mp (eq_zero_of_pow_eq_zero numerator)

theorem kg_conditional_zero (L : E →ₗ[ℂ] F) (output : PureVector F → Y)
    (x : PureVector E) (h : L x.val=0) : kgConditionalValue L output x=none := by
  classical
  unfold kgConditionalValue
  rw [dif_pos h]
end GenericFailure

theorem kg_extraction_right_product {a : Parameters} {A B : KGFamilyObject a}
    (K : KGExtraction a A) (test : KGFamilyCarrier B)
    (x : PureVector (KGFamilyCarrier A)) (y : PureVector (KGFamilyCarrier B)) :
    kgExtractionMap (.right K test) (kgRawTensor x y).val=
      inner ℂ test y.val • kgExtractionMap K x.val := by
  change kgExtractionMap K (kgRightContractionLM test (x.val ⊗ₜ[ℂ] y.val))=_
  rw [kg_right_contraction_tmul]
  exact (kgExtractionMap K).map_smul (inner ℂ test y.val) x.val

theorem kg_family_zero_extraction {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    {A : KGFamilyObject a} (K : KGExtraction a A) (x : PureVector (KGFamilyCarrier A))
    (π : WickMetricPathRoleProtocol Ω) (h : kgExtractionMap K x.val=0) :
    kgFamilyOutput a s Ω A x (.original K π)=.extraction none :=
  congrArg KGFamilyReadout.extraction
    (kg_conditional_zero (E := KGFamilyCarrier A) (F := fockCoreDomain a)
      (Y := WickRoleReadout) (kgExtractionMap K).toLinearMap
      (fun u => kgRawOriginalOutput a s Ω u π) x h)

namespace W9.RawRegisteredOrbit
variable {X Q V P : Type} (D : RawRegisteredOrbit X Q V P)

theorem nondegenerate_of_execution_failure (x : X) (π : Q)
    (h : D.kernel.FailureAt x (.execution π)) :
    D.references.incidenceSystem.Nondegenerate :=
  ⟨x,.execution π,(D.references.incidenceSystem.not_admissible_iff_failure _ _).mpr h⟩

theorem objecthood_of_execution_failure (x : X) (π : Q)
    (h : D.kernel.FailureAt x (.execution π)) :
    D.references.incidenceSystem.Determinate ∧ D.references.incidenceSystem.Nondegenerate ∧
      D.kernel.ReferenceUnique ∧ D.kernel.Nontrivial ∧
      AASC.Asymmetric D.kernel.StandingToFailure := by
  have nd := D.nondegenerate_of_execution_failure x π h
  have reference : D.references.incidenceSystem.ReferenceAt
      (x,RegisteredQuestion.execution (D.outgoing x)) :=
    ⟨D.probabilityValue (D.weight x x),D.raw_probability_standing x x⟩
  have objecthood := D.references.incidenceSystem.determinateNondegenerateObjecthood
    D.reference_determinate reference nd
  exact ⟨D.reference_determinate,nd,objecthood.2.2.1,
    objecthood.2.2.2.1,objecthood.2.2.2.2.1⟩
end W9.RawRegisteredOrbit

def kgFamilyVacuum (a : Parameters) : PureVector (fockCoreDomain a) :=
  kgRawOriginalEquiv a ⟨vacuumCore,vacuumCore_nonzero⟩

def kgFamilyParticle (a : Parameters) : PureVector (fockCoreDomain a) :=
  kgRawOriginalEquiv a ⟨oneParticleCore,oneParticleCore_nonzero⟩

theorem kg_family_vacuum_particle_inner (a : Parameters) :
    inner ℂ (kgFamilyVacuum a).val (kgFamilyParticle a).val=0 := by
  exact kg_inner_zero_of_probability_zero _ _ (kg_raw_vacuum_particle_probability a)

attribute [local irreducible] kgFamilyVacuum kgFamilyParticle kgRawOriginalEquiv

def kgOrthogonalFailureQuestion (a : Parameters) (Ω : Opens CoordinatePoint) :
    KGFamilyQuestion a Ω (kgFamilyTensor (kgOriginalObject a) (kgOriginalObject a)) :=
  .original (.right .original (kgFamilyParticle a).val)
    (.original (.comparison 1 ⟨vacuumCore,vacuumCore_nonzero⟩))

theorem kg_actual_orthogonal_extraction_zero (a : Parameters) :
    kgExtractionMap (a := a)
      (A := kgFamilyTensor (kgOriginalObject a) (kgOriginalObject a))
      (.right .original (kgFamilyParticle a).val)
      (kgRawTensor (kgFamilyVacuum a) (kgFamilyVacuum a)).val=0 := by
  rw [kg_extraction_right_product,
    (inner_eq_zero_symm.mpr (kg_family_vacuum_particle_inner a)),zero_smul]

theorem kg_actual_orthogonal_failure_output (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) :
    kgFamilyOutput a s Ω (kgFamilyTensor (kgOriginalObject a) (kgOriginalObject a))
      (kgRawTensor (kgFamilyVacuum a) (kgFamilyVacuum a))
      (kgOrthogonalFailureQuestion a Ω)=.extraction none := by
  exact kg_family_zero_extraction s Ω _ _ _ (kg_actual_orthogonal_extraction_zero a)

theorem kg_actual_orthogonal_execution_failure (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) :
    (kgRawRegisteredOrbit a s Ω
      (kgFamilyTensor (kgOriginalObject a) (kgOriginalObject a))).kernel.FailureAt
        (kgRawTensor (kgFamilyVacuum a) (kgFamilyVacuum a))
        (.execution (kgOrthogonalFailureQuestion a Ω)) := by
  apply ((kgRawRegisteredOrbit a s Ω
    (kgFamilyTensor (kgOriginalObject a) (kgOriginalObject a))).execution_failure_iff
      (kgRawTensor (kgFamilyVacuum a) (kgFamilyVacuum a))
      (kgOrthogonalFailureQuestion a Ω)).mpr
  change ¬ kgFamilySuccess (kgFamilyOutput a s Ω
    (kgFamilyTensor (kgOriginalObject a) (kgOriginalObject a))
    (kgRawTensor (kgFamilyVacuum a) (kgFamilyVacuum a))
    (kgOrthogonalFailureQuestion a Ω))
  rw [kg_actual_orthogonal_failure_output]
  change ¬ some KGExecutionFailure.zeroExtraction=none
  exact Option.some_ne_none _

theorem kg_family_execution_nondegenerate (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) :
    (kgRawRegisteredOrbit a s Ω
      (kgFamilyTensor (kgOriginalObject a) (kgOriginalObject a))).references.incidenceSystem.Nondegenerate := by
  exact RawRegisteredOrbit.nondegenerate_of_execution_failure _ _ _
    (kg_actual_orthogonal_execution_failure a s Ω)

theorem kg_family_kernel_objecthood (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    let D := kgRawRegisteredOrbit a s Ω
      (kgFamilyTensor (kgOriginalObject a) (kgOriginalObject a))
    D.references.incidenceSystem.Determinate ∧ D.references.incidenceSystem.Nondegenerate ∧
      D.kernel.ReferenceUnique ∧ D.kernel.Nontrivial ∧
      AASC.Asymmetric D.kernel.StandingToFailure := by
  exact RawRegisteredOrbit.objecthood_of_execution_failure _ _ _
    (kg_actual_orthogonal_execution_failure a s Ω)

end AASCKleinGordon
