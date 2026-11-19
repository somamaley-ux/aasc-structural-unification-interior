import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic.NormNum

/-! A three-dimensional group of proper linear isometries transitive on the
unit frontier contains every proper rotation. No topological group closure
is used. The quadratic form is the one already reconstructed from the source. -/
namespace AASCInertial.RestRotations

noncomputable section
set_option linter.unusedSectionVars false
open Submodule Module
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
abbrev Iso (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] := E ≃ₗᵢ[ℝ] E

def determinant (A : Iso E) : ℝ := LinearMap.det A.toLinearMap
private def inversion : Iso E := LinearIsometryEquiv.neg ℝ
private def planeReflection (v : E) : Iso E := (ℝ ∙ v)ᗮ.reflection
private def halfTurn (v : E) : Iso E := (ℝ ∙ v).reflection

@[simp] private theorem determinant_mul (A B : Iso E) :
    determinant (A * B) = determinant A * determinant B := by
  change LinearMap.det (A.toLinearMap.comp B.toLinearMap) = _
  exact LinearMap.det_comp _ _

@[simp] private theorem determinant_one : determinant (1 : Iso E) = 1 :=
  LinearMap.det_id

@[simp] private theorem determinant_inversion (h3 : finrank ℝ E = 3) :
    determinant (inversion : Iso E) = -1 := by
  rw [inversion, ← Submodule.reflection_bot (E := E), determinant, Submodule.det_reflection]
  have dim := (⊥ : Submodule ℝ E).finrank_add_finrank_orthogonal
  have dim3 : finrank ℝ (⊥ : Submodule ℝ E)ᗮ = 3 := by simpa [h3] using dim
  rw [dim3]
  norm_num

@[simp] private theorem determinant_plane (v : E) (hv : v ≠ 0) :
    determinant (planeReflection v) = -1 := by
  rw [planeReflection, determinant, Submodule.det_reflection, Submodule.orthogonal_orthogonal,
    finrank_span_singleton hv, pow_one]

@[simp] private theorem plane_zero : planeReflection (0 : E) = 1 := by
  ext x
  simp only [planeReflection,Submodule.span_zero_singleton,Submodule.bot_orthogonal_eq_top]
  exact Submodule.reflection_mem_subspace_eq_self (Submodule.mem_top : x ∈ (⊤ : Submodule ℝ E))

@[simp] private theorem inversion_twice (A : Iso E) :
    inversion * (inversion * A) = A := by
  ext x
  simp [inversion]

private theorem inversion_commute (A : Iso E) : inversion * A = A * inversion := by
  ext x
  simp [inversion]

private theorem inversion_plane (v : E) : inversion * planeReflection v = halfTurn v := by
  ext x
  simp [inversion, planeReflection, halfTurn,
    Submodule.reflection_orthogonal_apply]

private theorem short_word (l : List E) (len : l.length ≤ 2)
    (orientation : determinant (l.map planeReflection).prod = -1) :
    ∃ v : E, v ≠ 0 ∧ (l.map planeReflection).prod = planeReflection v := by
  cases l with
  | nil => norm_num at orientation
  | cons u l =>
    cases l with
    | nil =>
      by_cases hu : u = 0
      · subst u; norm_num at orientation
      · exact ⟨u,hu,by simp⟩
    | cons v l =>
      cases l with
      | cons w l => simp at len; omega
      | nil =>
        by_cases hu : u = 0 <;> by_cases hv : v = 0
        · subst u; subst v; norm_num at orientation
        · subst u; exact ⟨v,hv,by simp⟩
        · subst v; exact ⟨u,hu,by simp⟩
        · norm_num [determinant_plane _ hu, determinant_plane _ hv] at orientation

private theorem all_proper_of_half_turns (H : Subgroup (Iso E))
    (axes : ∀ v : E, v ≠ 0 → halfTurn v ∈ H) (A : Iso E) (hA : determinant A = 1) :
    A ∈ H := by
  obtain ⟨l, _, hword⟩ := A.reflections_generate_dim
  change A = (l.map planeReflection).prod at hword
  subst A
  have words (s : List E) :
      let X := (s.map planeReflection).prod
      (determinant X = 1 ∧ X ∈ H) ∨ (determinant X = -1 ∧ inversion * X ∈ H) := by
    induction s with
    | nil => exact Or.inl ⟨by simp,H.one_mem⟩
    | cons v t ih =>
      dsimp only at ih ⊢
      by_cases hv : v = 0
      · subst v; simpa using ih
      simp only [List.map_cons, List.prod_cons, determinant_mul, determinant_plane v hv]
      rcases ih with ⟨hd,hm⟩ | ⟨hd,hm⟩
      · refine Or.inr ⟨by rw [hd]; norm_num,?_⟩
        rw [← mul_assoc,inversion_plane]
        exact H.mul_mem (axes v hv) hm
      · refine Or.inl ⟨by rw [hd]; norm_num,?_⟩
        have hh := H.mul_mem (axes v hv) hm
        rw [← inversion_plane, inversion_commute (planeReflection v), mul_assoc, inversion_twice] at hh
        exact hh
  rcases words l with ⟨_,h⟩ | ⟨hd,_⟩
  · exact h
  · rw [hA] at hd; norm_num at hd

/-- The group acts on the actual unit frontier of the reconstructed form. -/
def FrontierTransitive (H : Subgroup (Iso E)) : Prop :=
  ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → ∃ A ∈ H, A x = y

private theorem half_turn_seed (H : Subgroup (Iso E)) (h3 : finrank ℝ E = 3)
    (proper : ∀ A ∈ H, determinant A = 1) (transitive : FrontierTransitive H)
    (x : E) (hx : ‖x‖ = 1) : ∃ v : E, v ≠ 0 ∧ halfTurn v ∈ H := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  obtain ⟨A,hA,ha⟩ := transitive x (-x) hx (by simpa using hx)
  let S : Iso E := inversion * A
  have hxS : S x = x := by simp [S, inversion, ha]
  let K := (ContinuousLinearMap.id ℝ E - S.toContinuousLinearEquiv.toContinuousLinearMap).ker
  have hxK : x ∈ K := by change x - S x = 0; rw [hxS, sub_self]
  have hle : (ℝ ∙ x) ≤ K := (Submodule.span_singleton_le_iff_mem x K).mpr hxK
  have hpos := Submodule.finrank_mono hle
  rw [finrank_span_singleton hx0] at hpos
  have := K.finrank_add_finrank_orthogonal
  have dim : finrank ℝ Kᗮ ≤ 2 := by omega
  obtain ⟨l,len,eqS⟩ := S.reflections_generate_dim_aux dim
  change S = (l.map planeReflection).prod at eqS
  have hor : determinant S = -1 := by simp [S, proper A hA, determinant_inversion h3]
  obtain ⟨v,hv,eqv⟩ := short_word l len (eqS ▸ hor)
  have h : S = planeReflection v := eqS.trans eqv
  have hvA : A = halfTurn v := by
    calc A = inversion * S := (inversion_twice A).symm
         _ = halfTurn v := by rw [h,inversion_plane]
  exact ⟨v,hv,hvA ▸ hA⟩

private theorem all_axes_of_seed (H : Subgroup (Iso E)) (transitive : FrontierTransitive H)
    (u : E) (hu : u ≠ 0) (seed : halfTurn u ∈ H)
    (v : E) (hv : v ≠ 0) : halfTurn v ∈ H := by
  obtain ⟨A,hA,ha⟩ := transitive (‖u‖⁻¹ • u) (‖v‖⁻¹ • v)
    (norm_smul_inv_norm hu) (norm_smul_inv_norm hv)
  have line (w : E) (hw : w ≠ 0) : (ℝ ∙ ‖w‖⁻¹ • w) = ℝ ∙ w :=
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr hw))) w
  have hmap : (ℝ ∙ u).map A.toLinearMap = ℝ ∙ v := by
    rw [← line u hu,← line v hv,Submodule.map_span]
    simp [ha]
  have conj := Submodule.reflection_map A (ℝ ∙ u)
  change ((ℝ ∙ u).map A.toLinearMap).reflection = A * halfTurn u * A⁻¹ at conj
  have e : halfTurn v = A * halfTurn u * A⁻¹ :=
    (congrArg (fun K : Submodule ℝ E => K.reflection) hmap).symm.trans conj
  rw [e]
  exact H.mul_mem (H.mul_mem hA seed) (H.inv_mem hA)

/-- Corollary 5.8 of the SR companion on a real three-dimensional spatial receiver.
The actual subgroup of comparison maps contains every proper linear isometry. -/
theorem proper_rotations_of_transitive_frontier (H : Subgroup (Iso E))
    (h3 : finrank ℝ E = 3) (proper : ∀ A ∈ H, determinant A = 1)
    (transitive : FrontierTransitive H) (A : Iso E) : A ∈ H ↔ determinant A = 1 := by
  refine ⟨proper A, fun hA => ?_⟩
  haveI : Nontrivial E := nontrivial_of_finrank_pos (by omega : 0 < finrank ℝ E)
  obtain ⟨x,hx⟩ := exists_ne (0 : E)
  obtain ⟨u,hu,seed⟩ := half_turn_seed H h3 proper transitive
    (‖x‖⁻¹ • x) (norm_smul_inv_norm hx)
  exact all_proper_of_half_turns H (all_axes_of_seed H transitive u hu seed) A hA

#print axioms proper_rotations_of_transitive_frontier

end
end AASCInertial.RestRotations
