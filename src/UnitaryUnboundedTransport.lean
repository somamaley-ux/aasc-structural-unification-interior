import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.LinearMap

noncomputable section
open LinearPMap
namespace AASCSpatial
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def unitaryTransport (U : H ≃ₗᵢ[ℂ] K) (T : H →ₗ.[ℂ] H) : K →ₗ.[ℂ] K where
  domain := T.domain.comap U.symm.toLinearMap
  toFun :=
    { toFun := fun y => U (T ⟨U.symm y.val,y.prop⟩)
      map_add' := by
        intro x y
        have h : (⟨U.symm (x+y).val,(x+y).prop⟩ : T.domain) =
            ⟨U.symm x.val,x.prop⟩+⟨U.symm y.val,y.prop⟩ := Subtype.ext (U.symm.map_add _ _)
        change U (T _) = U (T _)+U (T _)
        rw [h,T.map_add,U.map_add]
      map_smul' := by
        intro c x
        have h : (⟨U.symm (c • x).val,(c • x).prop⟩ : T.domain) =
            c • ⟨U.symm x.val,x.prop⟩ := Subtype.ext (U.symm.map_smul _ _)
        change U (T _) = c • U (T _)
        rw [h,T.map_smul,U.map_smul] }

@[simp] theorem unitaryTransport_apply (U : H ≃ₗᵢ[ℂ] K) (T : H →ₗ.[ℂ] H)
    (y : (unitaryTransport U T).domain) :
    unitaryTransport U T y = U (T ⟨U.symm y.val,y.prop⟩) := rfl

def unitaryTransportOriginal (U : H ≃ₗᵢ[ℂ] K) (T : H →ₗ.[ℂ] H) (x : T.domain) :
    (unitaryTransport U T).domain :=
  ⟨U x.val,by change U.symm (U x.val) ∈ T.domain; simpa using x.prop⟩

@[simp] theorem unitaryTransport_on_original (U : H ≃ₗᵢ[ℂ] K) (T : H →ₗ.[ℂ] H) (x : T.domain) :
    unitaryTransport U T (unitaryTransportOriginal U T x)=U (T x) := by
  rw [unitaryTransport_apply]
  congr 2
  apply Subtype.ext
  exact U.symm_apply_apply x.val

theorem unitaryTransport_dense (U : H ≃ₗᵢ[ℂ] K) (T : H →ₗ.[ℂ] H)
    (hT : Dense (T.domain : Set H)) : Dense ((unitaryTransport U T).domain : Set K) := by
  have h := U.surjective.denseRange.comp hT.denseRange_val U.continuous
  intro y
  apply closure_mono (t:=((unitaryTransport U T).domain : Set K)) _ (h y)
  rintro z ⟨x,rfl⟩
  exact (unitaryTransportOriginal U T x).prop

theorem unitaryTransport_symmetric (U : H ≃ₗᵢ[ℂ] K) (T : H →ₗ.[ℂ] H)
    (hT : T.IsFormalAdjoint T) :
    (unitaryTransport U T).IsFormalAdjoint (unitaryTransport U T) := by
  intro x y
  let a : T.domain := ⟨U.symm x.val,x.prop⟩
  let b : T.domain := ⟨U.symm y.val,y.prop⟩
  change inner ℂ (U (T a)) y.val = inner ℂ x.val (U (T b))
  rw [← U.apply_symm_apply y.val,← U.apply_symm_apply x.val,U.inner_map_map,U.inner_map_map]
  exact hT a b

theorem unitaryTransport_selfAdjoint (U : H ≃ₗᵢ[ℂ] K) (T : H →ₗ.[ℂ] H)
    (hT : IsSelfAdjoint T) : IsSelfAdjoint (unitaryTransport U T) := by
  have hd := hT.dense_domain
  have hS := unitaryTransport_dense U T hd
  have hTstar : T.adjoint=T := LinearPMap.isSelfAdjoint_def.mp hT
  have hformal : T.IsFormalAdjoint T := by
    have h := LinearPMap.adjoint_isFormalAdjoint hd
    rwa [hTstar] at h
  have lower := (unitaryTransport_symmetric U T hformal).le_adjoint hS
  have upper : (unitaryTransport U T).adjoint ≤ unitaryTransport U T := by
    apply LinearPMap.le_of_le_graph
    intro z hz
    obtain ⟨y,rfl⟩ := (LinearPMap.mem_graph_iff' _).mp hz
    let w := (unitaryTransport U T).adjoint y
    have hp : ∀ x : T.domain,inner ℂ (U.symm w) x.val = inner ℂ (U.symm y.val) (T x) := by
      intro x
      calc
        inner ℂ (U.symm w) x.val = inner ℂ w (U x.val) := by
          simpa only [U.apply_symm_apply] using (U.inner_map_map (U.symm w) x.val).symm
        _ = inner ℂ y.val (U (T x)) := by
          have h := LinearPMap.adjoint_isFormalAdjoint hS y (unitaryTransportOriginal U T x)
          simpa only [unitaryTransport_on_original] using h
        _ = inner ℂ (U.symm y.val) (T x) := by
          simpa only [U.apply_symm_apply] using U.inner_map_map (U.symm y.val) (T x)
    have hy : U.symm y.val ∈ T.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨U.symm w,hp⟩
    have hyT : U.symm y.val ∈ T.domain := by rwa [hTstar] at hy
    have hv := LinearPMap.adjoint_apply_eq hd ⟨U.symm y.val,hy⟩ hp
    have hvT : T ⟨U.symm y.val,hyT⟩=U.symm w := by
      have hg : (U.symm y.val,U.symm w) ∈ T.adjoint.graph := by
        exact hv ▸ (LinearPMap.mem_graph T.adjoint ⟨U.symm y.val,hy⟩)
      rw [hTstar] at hg
      exact LinearPMap.mem_graph_snd_inj T (LinearPMap.mem_graph T ⟨U.symm y.val,hyT⟩) hg rfl
    apply (LinearPMap.mem_graph_iff' _).mpr
    refine ⟨⟨y.val,hyT⟩,?_⟩
    apply Prod.ext
    · rfl
    change U (T ⟨U.symm y.val,hyT⟩)=w
    rw [hvT,U.apply_symm_apply]
  exact LinearPMap.isSelfAdjoint_def.mpr (le_antisymm upper lower)

end AASCSpatial
