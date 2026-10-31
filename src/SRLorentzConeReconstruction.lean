import SRConeClockBody
import SRSpatialCoordinateIndependence

/-! SR 5.7: original cone -> constructed spatial form -> Lorentz quadratic
form, with exact agreement on the whole future cone. The dimension is arbitrary
finite with a nonzero spatial kernel. No quadratic cone is an input. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open Set
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

def srClockSpatialPart (τ : V →L[ℝ] ℝ) (e : V) (clockOne : τ e=1) :
    V →ₗ[ℝ] SRClockSpatialSpace τ where
  toFun v:=⟨v-τ v • e,by
    change τ (v-τ v • e)=0
    simp [clockOne,smul_eq_mul]⟩
  map_add' v w:=by
    apply Subtype.ext
    change (v+w)-τ (v+w) • e=(v-τ v • e)+(w-τ w • e)
    rw [map_add,add_smul]
    abel
  map_smul' r v:=by
    apply Subtype.ext
    change r • v-τ (r • v) • e=r • (v-τ v • e)
    simp [smul_sub,smul_smul,smul_eq_mul]

theorem sr_original_clock_spatial_decomposition (τ : V →L[ℝ] ℝ) (e : V)
    (clockOne : τ e=1) (v : V) :
    τ v • e+(srClockSpatialPart τ e clockOne v:V)=v := by
  change τ v • e+(v-τ v • e)=v
  abel

theorem sr_clock_spatial_part_rest_zero (τ : V →L[ℝ] ℝ) (e : V)
    (clockOne : τ e=1) : srClockSpatialPart τ e clockOne e=0 := by
  apply Subtype.ext
  change e-τ e • e=0
  simp [clockOne]

def srConstructedLorentzQuadratic (τ : V →L[ℝ] ℝ) (e : V) (clockOne : τ e=1)
    (G : QuadraticForm ℝ (SRClockSpatialSpace τ)) : QuadraticForm ℝ V:=
  QuadraticMap.linMulLin τ.toLinearMap τ.toLinearMap-G.comp (srClockSpatialPart τ e clockOne)

theorem sr_constructed_lorentz_quadratic_value (τ : V →L[ℝ] ℝ) (e : V)
    (clockOne : τ e=1) (G : QuadraticForm ℝ (SRClockSpatialSpace τ)) (v : V) :
    srConstructedLorentzQuadratic τ e clockOne G v=
      (τ v)^2-G (srClockSpatialPart τ e clockOne v) := by
  change τ v*τ v-G (srClockSpatialPart τ e clockOne v)=_
  ring

theorem sr_full_clock_body_recovers_entire_future_cone
    (C : Set V) (conic : ∀ r:ℝ,0≤r → ∀ v∈C,r • v∈C)
    (τ : V →L[ℝ] ℝ) (positive : ∀ v∈C,v≠0 → 0<τ v)
    (e : V) (restInCone : e∈C) (clockOne : τ e=1)
    (G : QuadraticForm ℝ (SRClockSpatialSpace τ)) (gpositive : G.PosDef)
    (body : ∀ x,x∈srCenteredClockBody C τ e ↔ G x≤1) (v : V) :
    v∈C ↔ 0≤τ v ∧ G (srClockSpatialPart τ e clockOne v)≤(τ v)^2 := by
  have hzero:(0:V)∈C:=by simpa using conic 0 (by norm_num) e restInCone
  let x:SRClockSpatialSpace τ:=srClockSpatialPart τ e clockOne v
  let t:ℝ:=τ v
  have hdecomp:t • e+(x:V)=v:=sr_original_clock_spatial_decomposition τ e clockOne v
  have hnorm (ht:0<t):e+((t⁻¹ • x:SRClockSpatialSpace τ):V)=t⁻¹ • v:=by
    change e+t⁻¹ • (v-τ v • e)=t⁻¹ • v
    rw [smul_sub,smul_smul]
    change e+(t⁻¹ • v-(t⁻¹*t) • e)=t⁻¹ • v
    rw [inv_mul_cancel₀ ht.ne',one_smul]
    abel
  constructor
  · intro hv
    by_cases hz:v=0
    · simp [hz]
    · have ht:0<t:=positive v hv hz
      have hbody:t⁻¹ • x∈srCenteredClockBody C τ e:=by
        change e+((t⁻¹ • x:SRClockSpatialSpace τ):V)∈C
        rw [hnorm ht]
        exact conic t⁻¹ (inv_nonneg.mpr ht.le) v hv
      have hg: (t⁻¹*t⁻¹)*G x≤1:=by
        have hh:=(body _).mp hbody
        rw [G.map_smul] at hh
        exact hh
      have hm:=mul_le_mul_of_nonneg_left hg (mul_self_nonneg t)
      have he:(t*t)*((t⁻¹*t⁻¹)*G x)=G x:=by field_simp
      rw [he,mul_one] at hm
      exact ⟨ht.le,by simpa only [pow_two] using hm⟩
  · rintro ⟨ht,hg⟩
    change 0≤t at ht
    change G x≤t^2 at hg
    by_cases hz:t=0
    · have hx:x=0:=by
        by_contra hn
        have hp:=gpositive x hn
        rw [hz] at hg
        norm_num at hg
        linarith
      have hv:v=0:=by
        rw [hz,hx] at hdecomp
        simpa using hdecomp.symm
      simpa only [hv] using hzero
    · have htp:0<t:=lt_of_le_of_ne ht (Ne.symm hz)
      have hgn:G (t⁻¹ • x)≤1:=by
        rw [G.map_smul]
        change (t⁻¹*t⁻¹)*G x≤1
        have hm:=mul_le_mul_of_nonneg_left hg (mul_self_nonneg t⁻¹)
        have he:(t⁻¹*t⁻¹)*t^2=1:=by field_simp
        rw [he] at hm
        exact hm
      have hb: t⁻¹ • x∈srCenteredClockBody C τ e:=(body _).mpr hgn
      have hc:=conic t htp.le (e+((t⁻¹ • x:SRClockSpatialSpace τ):V)) hb
      have he:t • (e+((t⁻¹ • x:SRClockSpatialSpace τ):V))=v:=by
        change t • (e+t⁻¹ • (x:V))=v
        rw [smul_add,smul_smul,mul_inv_cancel₀ hz,one_smul]
        exact hdecomp
      rwa [he] at hc

theorem sr_original_cone_full_isotropy_constructs_unique_spatial_and_lorentz_receipt
    (C : Set V) (closed : IsClosed C) (convex : Convex ℝ C)
    (conic : ∀ r:ℝ,0≤r → ∀ v∈C,r • v∈C)
    (τ : V →L[ℝ] ℝ) (positive : ∀ v∈C,v≠0 → 0<τ v)
    [Nontrivial (SRClockSpatialSpace τ)] (e : V) (interiorRest : e∈interior C)
    (clockOne : τ e=1) {H : Type*} (rest : H → V ≃L[ℝ] V)
    (clockPreserved : ∀ h v,τ (rest h v)=τ v) (restFixed : ∀ h,rest h e=e)
    (preserves : ∀ h,rest h '' C=C)
    (isotropy : ∀ x∈frontier (srCenteredClockBody C τ e),
      ∀ y∈frontier (srCenteredClockBody C τ e),
      ∃ h,srRestOnClockKernel τ (rest h) (clockPreserved h) x=y) :
    ∃! G:QuadraticForm ℝ (SRClockSpatialSpace τ),G.PosDef ∧
      (∀ x,x∈srCenteredClockBody C τ e ↔ G x≤1) ∧
      (∀ h x,G (srRestOnClockKernel τ (rest h) (clockPreserved h) x)=G x) ∧
      ∀ v,v∈C ↔ 0≤τ v ∧ 0≤srConstructedLorentzQuadratic τ e clockOne G v := by
  obtain ⟨G,hG,unique⟩:=sr_arbitrary_finite_dimensional_isotropic_body_constructs_unique_form
    (srCenteredClockBody C τ e) (sr_clock_body_compact C closed conic τ positive e clockOne)
    (sr_clock_body_convex C convex τ e) (sr_clock_body_zero_interior C τ e interiorRest)
    (fun h=>srRestOnClockKernel τ (rest h) (clockPreserved h))
    (fun h=>sr_original_rest_preserves_constructed_clock_body C τ e (rest h)
      (clockPreserved h) (restFixed h) (preserves h)) isotropy
  refine ⟨G,⟨hG.1,hG.2.1,hG.2.2,?_⟩,?_⟩
  · intro v
    rw [sr_constructed_lorentz_quadratic_value]
    simpa only [sub_nonneg] using sr_full_clock_body_recovers_entire_future_cone
      C conic τ positive e (interior_subset interiorRest) clockOne G hG.1 hG.2.1 v
  · intro other ho
    exact unique other ⟨ho.1,ho.2.1,ho.2.2.1⟩

#print axioms srClockSpatialPart
#print axioms sr_original_clock_spatial_decomposition
#print axioms sr_clock_spatial_part_rest_zero
#print axioms sr_constructed_lorentz_quadratic_value
#print axioms sr_full_clock_body_recovers_entire_future_cone
#print axioms sr_original_cone_full_isotropy_constructs_unique_spatial_and_lorentz_receipt
end
end AASCMetricConstruction
