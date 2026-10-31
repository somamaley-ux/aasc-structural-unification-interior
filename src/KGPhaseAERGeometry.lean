import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! Phase reduction on a general complex inner-product carrier. The unit
representative is a slice; no original standing/admission gate is defined. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped ComplexConjugate
namespace AASCKleinGordon
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

def phaseAEROmega (v w : E) : ℝ := (inner ℂ v w).im

def phaseAERInnerImCLM (u : E) : E →L[ℝ] ℝ :=
  Complex.imCLM.comp ((innerSL ℂ u).restrictScalars ℝ)

def phaseAERInnerReCLM (u : E) : E →L[ℝ] ℝ :=
  Complex.reCLM.comp ((innerSL ℂ u).restrictScalars ℝ)

@[simp] theorem phaseAER_inner_im_apply (u v : E) :
    phaseAERInnerImCLM u v = (inner ℂ u v).im := rfl
@[simp] theorem phaseAER_inner_re_apply (u v : E) :
    phaseAERInnerReCLM u v = (inner ℂ u v).re := rfl

def phaseAERTangent (u : E) : Submodule ℝ E := (phaseAERInnerReCLM u).ker

def phaseAERHorizontal (u : E) : Submodule ℝ E :=
  (((innerSL ℂ u).restrictScalars ℝ).toLinearMap).ker

def phaseAERPhaseDirection (u : E) : E := Complex.I • u

def phaseAERVertical (u : E) : Submodule ℝ E :=
  Submodule.span ℝ {phaseAERPhaseDirection u}

def phaseAERQ (u : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (phaseAERInnerImCLM u).smulRight (phaseAERPhaseDirection u)

@[simp] theorem phaseAER_q_apply (u v : E) :
    phaseAERQ u v = v - (inner ℂ u v).im • (Complex.I • u) := rfl
@[simp] theorem phaseAER_mem_tangent (u v : E) :
    v ∈ phaseAERTangent u ↔ (inner ℂ u v).re = 0 := Iff.rfl
@[simp] theorem phaseAER_mem_horizontal (u v : E) :
    v ∈ phaseAERHorizontal u ↔ inner ℂ u v = 0 := Iff.rfl

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem phaseAER_omega_add_left (v w z : E) :
    phaseAEROmega (v+w) z = phaseAEROmega v z + phaseAEROmega w z := by
  change (inner ℂ (v+w) z).im = _
  rw [inner_add_left,Complex.add_im]
  rfl
omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem phaseAER_omega_add_right (v w z : E) :
    phaseAEROmega v (w+z) = phaseAEROmega v w + phaseAEROmega v z := by
  change (inner ℂ v (w+z)).im = _
  rw [inner_add_right,Complex.add_im]
  rfl
theorem phaseAER_omega_smul_left (r : ℝ) (v w : E) :
    phaseAEROmega (r • v) w = r*phaseAEROmega v w := by
  simp [phaseAEROmega,inner_smul_left_eq_smul]
theorem phaseAER_omega_smul_right (r : ℝ) (v w : E) :
    phaseAEROmega v (r • w) = r*phaseAEROmega v w := by
  simp [phaseAEROmega,inner_smul_right_eq_smul]
omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem phaseAER_omega_self (v : E) : phaseAEROmega v v = 0 := by
  exact inner_self_im (𝕜 := ℂ) v
omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem phaseAER_omega_skew (v w : E) : phaseAEROmega v w = -phaseAEROmega w v := by
  exact inner_im_symm (𝕜 := ℂ) v w

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem phaseAER_omega_continuous : Continuous (fun vw : E×E => phaseAEROmega vw.1 vw.2) :=
  Complex.continuous_im.comp (continuous_fst.inner (𝕜 := ℂ) continuous_snd)

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem phaseAER_omega_I_left (u v : E) :
    phaseAEROmega (Complex.I • u) v = -(inner ℂ u v).re := by
  change (inner ℂ (Complex.I • u) v).im = _
  rw [inner_smul_left]
  simp [Complex.mul_im]
omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem phaseAER_omega_I_self (v : E) :
    phaseAEROmega v (Complex.I • v) = ‖v‖^2 := by
  rw [phaseAEROmega,inner_smul_right]
  simp only [Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm

theorem phaseAER_horizontal_tangent (u v : E) (hv : v ∈ phaseAERHorizontal u) :
    v ∈ phaseAERTangent u := by
  change (inner ℂ u v).re = 0
  rw [(phaseAER_mem_horizontal u v).mp hv]
  rfl

theorem phaseAER_horizontal_I (u v : E) (hv : v ∈ phaseAERHorizontal u) :
    Complex.I • v ∈ phaseAERHorizontal u := by
  change inner ℂ u (Complex.I • v) = 0
  rw [inner_smul_right,(phaseAER_mem_horizontal u v).mp hv,mul_zero]

theorem phaseAER_phase_tangent (u : E) : Complex.I • u ∈ phaseAERTangent u := by
  change (inner ℂ u (Complex.I • u)).re = 0
  rw [inner_smul_right]
  simp only [Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub]
  have hh : (inner ℂ u u).im=0 := inner_self_im (𝕜 := ℂ) u
  rw [hh]
  exact neg_zero

theorem phaseAER_q_horizontal (u : E) (hu : ‖u‖=1) (v : E)
    (hv : v ∈ phaseAERTangent u) : phaseAERQ u v ∈ phaseAERHorizontal u := by
  have huu : inner ℂ u u = 1 := by simp [inner_self_eq_norm_sq_to_K,hu]
  change inner ℂ u (v-(inner ℂ u v).im • (Complex.I • u)) = 0
  rw [inner_sub_right,inner_smul_right_eq_smul,inner_smul_right,huu,mul_one]
  apply Complex.ext
  · simpa using (phaseAER_mem_tangent u v).mp hv
  · simp

theorem phaseAER_q_horizontal_id (u v : E) (hv : v ∈ phaseAERHorizontal u) :
    phaseAERQ u v = v := by
  rw [phaseAER_q_apply,(phaseAER_mem_horizontal u v).mp hv]
  simp

def phaseAERQHorizontal (u : E) (hu : ‖u‖=1) :
    phaseAERTangent u →L[ℝ] phaseAERHorizontal u :=
  ((phaseAERQ u).comp (phaseAERTangent u).subtypeL).codRestrict
    (phaseAERHorizontal u) (fun v => phaseAER_q_horizontal u hu v v.property)

theorem phaseAER_q_surjective (u : E) (hu : ‖u‖=1) :
    Function.Surjective (phaseAERQHorizontal u hu) := by
  intro w
  refine ⟨⟨w,phaseAER_horizontal_tangent u w w.property⟩,?_⟩
  apply Subtype.ext
  exact phaseAER_q_horizontal_id u w w.property

theorem phaseAER_q_zero_iff_vertical (u : E) (hu : ‖u‖=1) (v : E) :
    phaseAERQ u v = 0 ↔ v ∈ phaseAERVertical u := by
  have huu : inner ℂ u u = 1 := by simp [inner_self_eq_norm_sq_to_K,hu]
  constructor
  · intro hv
    have h : v = (inner ℂ u v).im • phaseAERPhaseDirection u := sub_eq_zero.mp hv
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · intro hv
    obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hv
    rw [← hr]
    change phaseAERQ u (r • (Complex.I • u)) = 0
    rw [phaseAER_q_apply]
    have hz : (inner ℂ u (r • (Complex.I • u))).im = r := by
      rw [inner_smul_right_eq_smul,inner_smul_right,huu,mul_one]
      simp
    rw [hz,sub_self]

theorem phaseAER_q_preserves_restricted_omega (u v w : E)
    (hw : w ∈ phaseAERTangent u) : phaseAEROmega (phaseAERQ u v) w = phaseAEROmega v w := by
  have hw' := (phaseAER_mem_tangent u w).mp hw
  rw [phaseAER_q_apply]
  change (inner ℂ (v-(inner ℂ u v).im • (Complex.I • u)) w).im = _
  rw [inner_sub_left,inner_smul_left_eq_smul]
  simp [inner_smul_left,Complex.mul_im,hw']
  rfl

theorem phaseAER_horizontal_nondegenerate (u v : E) (hv : v ∈ phaseAERHorizontal u)
    (h : ∀w : E,w ∈ phaseAERHorizontal u → phaseAEROmega v w = 0) : v = 0 := by
  have hz := h (Complex.I • v) (phaseAER_horizontal_I u v hv)
  rw [phaseAER_omega_I_self] at hz
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

theorem phaseAER_restricted_radical_iff (u : E) (hu : ‖u‖=1) (v : E)
    (hv : v ∈ phaseAERTangent u) :
    (∀w : E,w ∈ phaseAERTangent u → phaseAEROmega v w = 0) ↔
      v ∈ phaseAERVertical u := by
  rw [← phaseAER_q_zero_iff_vertical u hu v]
  constructor
  · intro h
    apply phaseAER_horizontal_nondegenerate u (phaseAERQ u v) (phaseAER_q_horizontal u hu v hv)
    intro w hw
    rw [phaseAER_q_preserves_restricted_omega u v w (phaseAER_horizontal_tangent u w hw)]
    exact h w (phaseAER_horizontal_tangent u w hw)
  · intro h w hw
    rw [← phaseAER_q_preserves_restricted_omega u v w hw,h]
    simp [phaseAEROmega]

theorem phaseAER_restricted_kernel_radical (u : E) (hu : ‖u‖=1) :
    {v : E | v ∈ phaseAERTangent u ∧
      ∀w : E,w ∈ phaseAERTangent u → phaseAEROmega v w = 0} =
        (phaseAERVertical u : Set E) := by
  ext v
  constructor
  · rintro ⟨hv,h⟩
    exact (phaseAER_restricted_radical_iff u hu v hv).mp h
  · intro hv
    have ht : phaseAERVertical u ≤ phaseAERTangent u := by
      apply Submodule.span_le.mpr
      intro w hw
      have he : w=phaseAERPhaseDirection u := Set.mem_singleton_iff.mp hw
      rw [he]
      exact phaseAER_phase_tangent u
    exact ⟨ht hv,(phaseAER_restricted_radical_iff u hu v (ht hv)).mpr hv⟩



def phaseAEROmegaBilin : E →ₗ[ℝ] E →ₗ[ℝ] ℝ where
  toFun v := { toFun := phaseAEROmega v
               map_add' := phaseAER_omega_add_right v
               map_smul' := fun r w => phaseAER_omega_smul_right r v w }
  map_add' v w := by ext z; exact phaseAER_omega_add_left v w z
  map_smul' r v := by ext w; exact phaseAER_omega_smul_left r v w

theorem phaseAER_q_ker (u : E) (hu : ‖u‖=1) :
    (phaseAERQ u).ker = phaseAERVertical u := by
  ext v
  exact phaseAER_q_zero_iff_vertical u hu v

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem phaseAER_omega_nondegenerate (v : E)
    (h : ∀w : E,phaseAEROmega v w=0) : v=0 := by
  have hz := h (Complex.I • v)
  rw [phaseAER_omega_I_self] at hz
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] in
theorem phaseAER_unitary_omega (U : E ≃ₗᵢ[ℂ] F) (v w : E) :
    phaseAEROmega (U v) (U w)=phaseAEROmega v w := by
  rw [phaseAEROmega,phaseAEROmega,U.inner_map_map]

theorem phaseAER_unitary_tangent (U : E ≃ₗᵢ[ℂ] F) (u v : E) :
    U v ∈ phaseAERTangent (U u) ↔ v ∈ phaseAERTangent u := by
  simp only [phaseAER_mem_tangent,U.inner_map_map]

theorem phaseAER_unitary_horizontal (U : E ≃ₗᵢ[ℂ] F) (u v : E) :
    U v ∈ phaseAERHorizontal (U u) ↔ v ∈ phaseAERHorizontal u := by
  simp only [phaseAER_mem_horizontal,U.inner_map_map]

theorem phaseAER_unitary_q (U : E ≃ₗᵢ[ℂ] F) (u v : E) :
    U (phaseAERQ u v)=phaseAERQ (U u) (U v) := by
  have hr (r : ℝ) (x : E) : U (r • x)=r • U x :=
    (U.toLinearEquiv.restrictScalars ℝ).map_smul r x
  rw [phaseAER_q_apply,map_sub,hr,U.map_smul,phaseAER_q_apply,U.inner_map_map]

#print axioms phaseAER_restricted_kernel_radical
#print axioms phaseAER_q_surjective
#print axioms phaseAER_horizontal_nondegenerate
end AASCKleinGordon
