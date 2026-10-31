import KGRawTensorCarrier

noncomputable section
namespace AASCKleinGordon
open scoped TensorProduct
open KGQuantum

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

instance kgRawRayTopology : TopologicalSpace (PhysicalRay E) :=
  inferInstanceAs (TopologicalSpace (Quotient (pureVectorSetoid E)))

def kgRawScalarAction : MulAction ℂˣ (PureVector E) where
  smul c x := PureVector.smul (c : ℂ) (Units.ne_zero c) x
  one_smul x := by apply Subtype.ext; exact one_smul ℂ x.val
  mul_smul c d x := by apply Subtype.ext; exact mul_smul (c : ℂ) (d : ℂ) x.val

theorem kg_raw_phase_probability (c d : ℂˣ) (x y : PureVector E) :
    transitionProbability (kgRawScalarAction.smul c x) (kgRawScalarAction.smul d y) =
      transitionProbability x y :=
  transitionProbability_smul (c : ℂ) (d : ℂ) (Units.ne_zero c) (Units.ne_zero d) x y

/-- Actual independent composition, landing in its own tensor object. -/
def kgRawTensor (x : PureVector E) (y : PureVector F) : PureVector (E ⊗[ℂ] F) :=
  ⟨x.val ⊗ₜ[ℂ] y.val,by
    apply norm_ne_zero_iff.mp
    rw [TensorProduct.norm_tmul]
    exact mul_ne_zero (norm_ne_zero_iff.mpr x.property) (norm_ne_zero_iff.mpr y.property)⟩

theorem kg_raw_tensor_scalar_equivariance (c d : ℂ) (hc : c ≠ 0) (hd : d ≠ 0)
    (x : PureVector E) (y : PureVector F) :
    kgRawTensor (PureVector.smul c hc x) (PureVector.smul d hd y) =
      PureVector.smul (c*d) (mul_ne_zero hc hd) (kgRawTensor x y) := by
  apply Subtype.ext
  simp only [kgRawTensor,PureVector.coe_smul,TensorProduct.smul_tmul',
    TensorProduct.tmul_smul,smul_smul]
  rw [mul_comm d c]

theorem kg_raw_tensor_weights_multiply (x z : PureVector E) (y w : PureVector F) :
    transitionProbability (kgRawTensor x y) (kgRawTensor z w) =
      transitionProbability x z * transitionProbability y w := by
  simp only [transitionProbability,kgRawTensor,TensorProduct.inner_tmul,
    TensorProduct.norm_tmul,norm_mul,mul_pow]
  ring

theorem kg_raw_probability_interval (x y : PureVector E) :
    0 ≤ transitionProbability x y ∧ transitionProbability x y ≤ 1 := by
  have hd : 0 < ‖x.val‖^2*‖y.val‖^2 :=
    mul_pos (sq_pos_of_pos (norm_pos_iff.mpr x.property))
      (sq_pos_of_pos (norm_pos_iff.mpr y.property))
  constructor
  · exact div_nonneg (sq_nonneg _) (le_of_lt hd)
  · apply (div_le_one hd).mpr
    calc
      ‖inner ℂ x.val y.val‖^2 ≤ (‖x.val‖*‖y.val‖)^2 := by
        gcongr
        exact norm_inner_le_norm _ _
      _ = _ := mul_pow _ _ _

theorem kg_raw_probability_continuous :
    Continuous (fun p : PureVector E × PureVector E => transitionProbability p.1 p.2) := by
  have left : Continuous (fun p : PureVector E × PureVector E => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have right : Continuous (fun p : PureVector E × PureVector E => p.2.val) :=
    continuous_subtype_val.comp continuous_snd
  exact ((left.inner right).norm.pow 2).div
    ((left.norm.pow 2).mul (right.norm.pow 2))
    (fun p => transitionProbability_denominator_ne_zero p.1 p.2)

/-- Reuses the existing exact raw profile/orbit theorem, without declaring
profile equality to be an additional source quotient. -/
theorem kg_raw_profiles_exact_orbits (x y : PureVector E) :
    ((∀ z,transitionProbability x z=transitionProbability y z) ∧
      (∀ z,transitionProbability z x=transitionProbability z y)) ↔
      rayMap E x=rayMap E y := by
  constructor
  · intro h
    apply ray_eq_of_transitionProfile_eq
    intro r
    induction r using Quotient.inductionOn with
    | _ z => exact h.1 z
  · intro h
    constructor <;> intro z
    · change rayTransitionProbability (rayMap E x) (rayMap E z)=
        rayTransitionProbability (rayMap E y) (rayMap E z)
      rw [h]
    · change rayTransitionProbability (rayMap E z) (rayMap E x)=
        rayTransitionProbability (rayMap E z) (rayMap E y)
      rw [h]

/-- Algebraic orbit coequalizer. Topological regularity remains a separate
coordinate; this theorem does not assume standing descent. -/
theorem kg_raw_orbit_coequalizer {Y : Type*} (f : PureVector E → Y)
    (hf : ∀ x y,PureVector.ScalarRel x y → f x=f y) :
    ∃! g : PhysicalRay E → Y,∀ x,g (rayMap E x)=f x := by
  refine ⟨Quotient.lift f hf,by intro x; rfl,?_⟩
  intro g hg
  funext r
  induction r using Quotient.inductionOn with
  | _ x => exact hg x

/-- Coequalizer in topological spaces for the declared norm-subspace carrier.
This does not replace the stronger metric-source LF regularity. -/
theorem kg_raw_continuous_orbit_coequalizer {Y : Type*} [TopologicalSpace Y]
    (f : PureVector E → Y) (hc : Continuous f)
    (hf : ∀ x y,PureVector.ScalarRel x y → f x=f y) :
    ∃! g : PhysicalRay E → Y,Continuous g ∧ ∀ x,g (rayMap E x)=f x := by
  refine ⟨Quotient.lift f hf,⟨?_,by intro x; rfl⟩,?_⟩
  · change Continuous (Quotient.lift f hf : Quotient (pureVectorSetoid E) → Y)
    exact hc.quotient_lift hf
  intro g hg
  funext r
  induction r using Quotient.inductionOn with
  | _ x => exact hg.2 x

end AASCKleinGordon
