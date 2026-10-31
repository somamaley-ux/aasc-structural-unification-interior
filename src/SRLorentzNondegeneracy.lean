import SRLorentzConeReconstruction

/-! SR 5.7's direct sum and nondegeneracy: the actual clock split is
constructed, and the associated symmetric Lorentz bilinear form has zero
radical. No signature/nondegenerate metric certificate is assumed. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
open Set

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

def srClockSplitEquiv (τ : V →L[ℝ] ℝ) (e : V) (clockOne : τ e=1) :
    V ≃ₗ[ℝ] ℝ × SRClockSpatialSpace τ where
  toFun v:=(τ v,srClockSpatialPart τ e clockOne v)
  invFun p:=p.1 • e+(p.2:V)
  map_add' v w:=by simp only [map_add,Prod.mk_add_mk]
  map_smul' r v:=by simp only [map_smul,Prod.smul_mk,smul_eq_mul,RingHom.id_apply]
  left_inv v:=sr_original_clock_spatial_decomposition τ e clockOne v
  right_inv p:=by
    have ht:τ (p.1 • e+(p.2:V))=p.1:=by
      rw [map_add,map_smul,clockOne,sr_spatial_clock_zero]
      simp
    apply Prod.ext
    · exact ht
    · apply Subtype.ext
      change p.1 • e+(p.2:V)-τ (p.1 • e+(p.2:V)) • e=(p.2:V)
      rw [ht]
      abel

theorem sr_constructed_lorentz_direct_sum_value (τ : V →L[ℝ] ℝ) (e : V)
    (clockOne : τ e=1) (G : QuadraticForm ℝ (SRClockSpatialSpace τ))
    (p : ℝ × SRClockSpatialSpace τ) :
    srConstructedLorentzQuadratic τ e clockOne G ((srClockSplitEquiv τ e clockOne).symm p)=
      p.1^2-G p.2 := by
  have he:srClockSplitEquiv τ e clockOne ((srClockSplitEquiv τ e clockOne).symm p)=p:=
    (srClockSplitEquiv τ e clockOne).apply_symm_apply p
  have ht:=congrArg Prod.fst he
  have hx:=congrArg Prod.snd he
  rw [sr_constructed_lorentz_quadratic_value]
  change τ ((srClockSplitEquiv τ e clockOne).symm p)=p.1 at ht
  change srClockSpatialPart τ e clockOne ((srClockSplitEquiv τ e clockOne).symm p)=p.2 at hx
  rw [ht,hx]

theorem sr_lorentz_associated_against_calibrated_rest (τ : V →L[ℝ] ℝ) (e : V)
    (clockOne : τ e=1) (G : QuadraticForm ℝ (SRClockSpatialSpace τ)) (v : V) :
    (srConstructedLorentzQuadratic τ e clockOne G).associated v e=τ v := by
  let Q:=srConstructedLorentzQuadratic τ e clockOne G
  have hh:=congrArg (fun B:V →ₗ[ℝ] V →ₗ[ℝ] ℝ=>B v e)
    (QuadraticMap.two_nsmul_associated ℝ Q)
  simp only [two_nsmul,LinearMap.add_apply] at hh
  change Q.associated v e+Q.associated v e=Q (v+e)-Q v-Q e at hh
  dsimp only [Q] at hh
  simp only [sr_constructed_lorentz_quadratic_value,map_add,clockOne,
    sr_clock_spatial_part_rest_zero,add_zero,map_zero,one_pow,sub_zero] at hh
  change Q.associated v e=τ v
  dsimp only [Q]
  nlinarith [hh]

theorem sr_constructed_lorentz_associated_nondegenerate (τ : V →L[ℝ] ℝ) (e : V)
    (clockOne : τ e=1) (G : QuadraticForm ℝ (SRClockSpatialSpace τ))
    (positive : G.PosDef) :
    (srConstructedLorentzQuadratic τ e clockOne G).associated.SeparatingLeft := by
  intro v hv
  have ht:τ v=0:=by
    rw [← sr_lorentz_associated_against_calibrated_rest τ e clockOne G v]
    exact hv e
  have hq:srConstructedLorentzQuadratic τ e clockOne G v=0:=by
    rw [← QuadraticMap.associated_eq_self_apply ℝ]
    exact hv v
  rw [sr_constructed_lorentz_quadratic_value,ht] at hq
  have hx:srClockSpatialPart τ e clockOne v=0:=by
    apply positive.anisotropic
    linarith
  have he:=sr_original_clock_spatial_decomposition τ e clockOne v
  rw [ht,hx] at he
  simpa using he.symm

#print axioms srClockSplitEquiv
#print axioms sr_constructed_lorentz_direct_sum_value
#print axioms sr_lorentz_associated_against_calibrated_rest
#print axioms sr_constructed_lorentz_associated_nondegenerate
end
end AASCMetricConstruction
