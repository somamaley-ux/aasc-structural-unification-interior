import DenseWeakDerivative
import UnitaryExactGeneratorConverse

noncomputable section
set_option maxHeartbeats 2400000
open scoped Topology
namespace AASCKleinGordon.UnitaryCore
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem inner_pullback (U : ℝ → H ≃ₗᵢ[ℂ] H)
    (hinv : ∀ t x,(U t).symm x=U (-t) x) (t : ℝ) (x y : H) :
    inner ℂ x (U t y) = inner ℂ (U (-t) x) y := by
  have h := (U t).inner_map_map ((U t).symm x) y
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  simpa only [hinv] using h

theorem adjoint_antitone_of_dense (T S : H →ₗ.[ℂ] H)
    (hd : Dense (T.domain : Set H)) (hle : T≤S) : S.adjoint≤T.adjoint := by
  have hs : Dense (S.domain : Set H) := hd.mono hle.1
  have hf : S.adjoint.IsFormalAdjoint T := by
    intro y x
    have h := LinearPMap.adjoint_isFormalAdjoint hs y ⟨x.val,hle.1 x.property⟩
    have he : S ⟨x.val,hle.1 x.property⟩ = T x := (hle.2 rfl).symm
    simpa only [he] using h
  exact hf.symm.le_adjoint hd

theorem adjoint_orbit_hasDerivAt
    (κ : ℂ) (hstar : star (-κ)=κ)
    (U : ℝ → H ≃ₗᵢ[ℂ] H) (hc : ∀ x,Continuous (fun t => U t x))
    (hinv : ∀ t x,(U t).symm x=U (-t) x)
    (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H))
    (hp : ∀ t (x : T.domain),U t x.val∈T.domain)
    (hcomm : ∀ t (x : T.domain),T ⟨U t x.val,hp t x⟩=U t (T x))
    (hf : ∀ (x : T.domain) r,HasDerivAt (fun t => U t x.val) (κ • U r (T x)) r)
    (y : T.adjoint.domain) (r : ℝ) :
    HasDerivAt (fun t => U t y.val) (κ • U r (T.adjoint y)) r := by
  apply hasDerivAt_of_dense_inner_derivative (fun x : T.domain => x.val) hd.denseRange_val
    (fun t => U t y.val) (fun t => κ • U t (T.adjoint y))
    (continuous_const.smul (hc _))
  intro x s
  have hn : HasDerivAt (fun t => U (-t) x.val) ((-κ) • U (-s) (T x)) s := by
    have h := (hf x (-s)).scomp s (hasDerivAt_neg s)
    simpa only [Function.comp_def,neg_one_smul,neg_smul,one_smul] using h
  have hh := hn.inner ℂ (hasDerivAt_const s y.val)
  have he : (fun t => inner ℂ (U (-t) x.val) y.val) =
      (fun t => inner ℂ x.val (U t y.val)) :=
    funext (fun t => (inner_pullback U hinv t x.val y.val).symm)
  rw [he] at hh
  have ha : inner ℂ (U (-s) (T x)) y.val = inner ℂ (U (-s) x.val) (T.adjoint y) := by
    have h := (LinearPMap.adjoint_isFormalAdjoint hd).symm ⟨U (-s) x.val,hp (-s) x⟩ y
    simpa only [hcomm] using h
  have hs' : (starRingEnd ℂ) (-κ)=κ := hstar
  simpa only [inner_zero_right,add_zero,zero_add,inner_smul_left,hs',ha,
    ← inner_pullback U hinv s x.val (T.adjoint y),inner_smul_right] using hh

theorem adjoint_selfAdjoint_of_unitary_core
    (κ : ℂ) (hκ : κ≠0) (hstar : star (-κ)=κ)
    (U : ℝ → H ≃ₗᵢ[ℂ] H) (hc : ∀ x,Continuous (fun t => U t x))
    (hzero : ∀ x,U 0 x=x) (hinv : ∀ t x,(U t).symm x=U (-t) x)
    (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H)) (hsym : T.IsFormalAdjoint T)
    (hp : ∀ t (x : T.domain),U t x.val∈T.domain)
    (hcomm : ∀ t (x : T.domain),T ⟨U t x.val,hp t x⟩=U t (T x))
    (hf : ∀ (x : T.domain) r,HasDerivAt (fun t => U t x.val) (κ • U r (T x)) r) :
    IsSelfAdjoint T.adjoint := by
  have hle : T≤T.adjoint := hsym.le_adjoint hd
  have hda : Dense (T.adjoint.domain : Set H) := hd.mono hle.1
  have hconj : (starRingEnd ℂ) κ = -κ := by
    have h : -(starRingEnd ℂ) κ = κ := by simpa only [map_neg] using hstar
    linear_combination -h
  have hsa : T.adjoint.IsFormalAdjoint T.adjoint := by
    intro x y
    have hx := adjoint_orbit_hasDerivAt κ hstar U hc hinv T hd hp hcomm hf x 0
    have hy := adjoint_orbit_hasDerivAt κ hstar U hc hinv T hd hp hcomm hf y 0
    have h := hx.inner ℂ hy
    have hconst : HasDerivAt (fun t => inner ℂ (U t x.val) (U t y.val)) 0 0 := by
      simpa only [LinearIsometryEquiv.inner_map_map] using
        hasDerivAt_const (0 : ℝ) (inner ℂ x.val y.val)
    have he := h.unique hconst
    simp only [hzero,inner_smul_left,inner_smul_right,hconj] at he
    have hm : κ*(inner ℂ x.val (T.adjoint y)-inner ℂ (T.adjoint x) y.val)=0 := by
      calc
        _ = (-κ)*inner ℂ (T.adjoint x) y.val+κ*inner ℂ x.val (T.adjoint y) := by ring
        _ = 0 := by simpa only [add_comm] using he
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hκ)).symm
  exact LinearPMap.isSelfAdjoint_def.mpr (le_antisymm
    (adjoint_antitone_of_dense T T.adjoint hd hle) (hsa.le_adjoint hda))

end AASCKleinGordon.UnitaryCore
