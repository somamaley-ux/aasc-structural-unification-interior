import OriginalEHPalatiniVariation
import OriginalEHVolumeCompatibility
import OriginalEHPalatiniDerivativeAlgebra

/-! The pointwise derivative of the actual weighted current and its
identification with the actual contracted Ricci variation. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Filter
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise

def ehWeightedInverse (g : MetricField) (p : CoordinatePoint) (a b : Fin 4) : ℝ :=
  coordinateVolumeDensity g p * (g p)⁻¹ a b

theorem eh_scalar_partial_mul (f k : CoordinatePoint → ℝ) (p : CoordinatePoint) (c : Fin 4)
    (hf : DifferentiableAt ℝ f p) (hk : DifferentiableAt ℝ k p) :
    scalarPartial (fun x => f x * k x) p c =
      scalarPartial f p c * k p + f p * scalarPartial k p c := by
  have hd := (hf.hasFDerivAt.mul hk.hasFDerivAt).fderiv
  change fderiv ℝ (fun x => f x * k x) p = _ at hd
  simp only [scalarPartial,hd,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

theorem eh_scalar_partial_sub (f k : CoordinatePoint → ℝ) (p : CoordinatePoint) (c : Fin 4)
    (hf : DifferentiableAt ℝ f p) (hk : DifferentiableAt ℝ k p) :
    scalarPartial (fun x => f x - k x) p c =
      scalarPartial f p c - scalarPartial k p c := by
  have hd := (hf.hasFDerivAt.sub hk.hasFDerivAt).fderiv
  change fderiv ℝ (fun x => f x - k x) p = _ at hd
  simp only [scalarPartial,hd,ContinuousLinearMap.sub_apply]

theorem eh_sum2_product_scalar_partial
    (F G : Fin 4 → Fin 4 → CoordinatePoint → ℝ) (p : CoordinatePoint) (c : Fin 4)
    (hf : ∀ a b, DifferentiableAt ℝ (F a b) p)
    (hg : ∀ a b, DifferentiableAt ℝ (G a b) p) :
    scalarPartial (fun x => ∑ a : Fin 4, ∑ b : Fin 4, F a b x * G a b x) p c =
      ∑ a : Fin 4, ∑ b : Fin 4,
        (scalarPartial (F a b) p c * G a b p + F a b p * scalarPartial (G a b) p c) := by
  have hd := HasFDerivAt.fun_sum (u := Finset.univ) (fun a _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun b _ =>
      (hf a b).hasFDerivAt.mul (hg a b).hasFDerivAt))
  have he := hd.fderiv
  change fderiv ℝ (fun x => ∑ a : Fin 4, ∑ b : Fin 4, F a b x * G a b x) p = _ at he
  simp only [scalarPartial,he,ContinuousLinearMap.sum_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem eh_weighted_inverse_smooth_at (g : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (p : CoordinatePoint) (negative : (g p).det < 0) (a b : Fin 4) :
    ContDiffAt ℝ ∞ (fun x => ehWeightedInverse g x a b) p :=
  (eh_volume_density_smooth_at g hg p negative).mul
    (eh_inverse_component_smooth_at g hg p (ne_of_lt negative) a b)

theorem eh_weighted_inverse_partial (g : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (p : CoordinatePoint) (negative : (g p).det < 0) (a b c : Fin 4) :
    scalarPartial (fun x => ehWeightedInverse g x a b) p c =
      coordinateVolumeDensity g p *
        ((∑ d : Fin 4, leviCivitaCoefficients g p d c d) * (g p)⁻¹ a b -
          (∑ d : Fin 4, leviCivitaCoefficients g p a c d * (g p)⁻¹ d b) -
          (∑ d : Fin 4, leviCivitaCoefficients g p b c d * (g p)⁻¹ a d)) := by
  unfold ehWeightedInverse
  rw [eh_scalar_partial_mul _ _ p c
    ((eh_volume_density_smooth_at g hg p negative).differentiableAt (by norm_num))
    ((eh_inverse_component_smooth_at g hg p (ne_of_lt negative) a b).differentiableAt (by norm_num)),
    eh_volume_partial_connection_trace g sg hg p negative c,
    eh_inverse_partial_compatible g sg hg p (ne_of_lt negative) a b c]
  ring

theorem eh_boundary_current_weighted (g h : MetricField) (p : CoordinatePoint) (c : Fin 4) :
    ehBoundaryCurrent g h p c =
      (∑ a : Fin 4, ∑ b : Fin 4, ehWeightedInverse g p a b * ehLCVariation g h p c a b) -
      (∑ a : Fin 4, ∑ b : Fin 4, ehWeightedInverse g p a c * ehLCVariation g h p b a b) := by
  simp only [ehBoundaryCurrent,ehWeightedInverse,mul_sub,Finset.mul_sum,mul_assoc]

theorem eh_current_component_actual_partial (g h : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (hh : ∀ a b, ContDiff ℝ ∞ (fun x => h x a b))
    (p : CoordinatePoint) (negative : (g p).det < 0) (c : Fin 4) :
    scalarPartial (fun x => ehBoundaryCurrent g h x c) p c =
      (∑ a : Fin 4, ∑ b : Fin 4,
        (scalarPartial (fun x => ehWeightedInverse g x a b) p c * ehLCVariation g h p c a b +
          ehWeightedInverse g p a b * scalarPartial (fun x => ehLCVariation g h x c a b) p c)) -
      (∑ a : Fin 4, ∑ b : Fin 4,
        (scalarPartial (fun x => ehWeightedInverse g x a c) p c * ehLCVariation g h p b a b +
          ehWeightedInverse g p a c * scalarPartial (fun x => ehLCVariation g h x b a b) p c)) := by
  have w (a b : Fin 4) := (eh_weighted_inverse_smooth_at g hg p negative a b).differentiableAt (by norm_num)
  have z (i a b : Fin 4) := (eh_lc_variation_smooth_at g h hg hh p
    (ne_of_lt negative) i a b).differentiableAt (by norm_num)
  have left : DifferentiableAt ℝ (fun x => ∑ a : Fin 4, ∑ b : Fin 4,
      ehWeightedInverse g x a b * ehLCVariation g h x c a b) p :=
    DifferentiableAt.fun_sum (fun a _ => DifferentiableAt.fun_sum (fun b _ =>
      (w a b).mul (z c a b)))
  have right : DifferentiableAt ℝ (fun x => ∑ a : Fin 4, ∑ b : Fin 4,
      ehWeightedInverse g x a c * ehLCVariation g h x b a b) p :=
    DifferentiableAt.fun_sum (fun a _ => DifferentiableAt.fun_sum (fun b _ =>
      (w a c).mul (z b a b)))
  have he : (fun x => ehBoundaryCurrent g h x c) = fun x =>
      (∑ a : Fin 4, ∑ b : Fin 4, ehWeightedInverse g x a b * ehLCVariation g h x c a b) -
      (∑ a : Fin 4, ∑ b : Fin 4, ehWeightedInverse g x a c * ehLCVariation g h x b a b) :=
    funext (fun x => eh_boundary_current_weighted g h x c)
  rw [he,eh_scalar_partial_sub _ _ p c left right]
  rw [eh_sum2_product_scalar_partial _ _ p c w (fun a b => z c a b),
    eh_sum2_product_scalar_partial _ _ p c (fun a _ => w a c) (fun a b => z b a b)]

theorem eh_actual_current_divergence_is_ricci_variation (g h : MetricField)
    (sg : MetricFieldSymmetric g) (sh : MetricFieldSymmetric h)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (hh : ∀ a b, ContDiff ℝ ∞ (fun x => h x a b))
    (p : CoordinatePoint) (negative : (g p).det < 0) :
    ehBoundaryDivergence g h p = coordinateVolumeDensity g p *
      (∑ a : Fin 4, ∑ b : Fin 4, (g p)⁻¹ a b * ehRicciVariation g h p a b) := by
  let B : Tensor2 := (g p)⁻¹
  let Γ := leviCivitaCoefficients g p
  let Z := ehLCVariation g h p
  let D := fun a b c r => scalarPartial (fun x => ehLCVariation g h x a b c) p r
  have ds : ∀ a b c r, D a b c r = D a c b r := by
    intro a b c r
    have he : (fun x => ehLCVariation g h x a b c) =
        fun x => ehLCVariation g h x a c b :=
      funext (fun x => eh_lc_variation_lower_symmetric g h sg sh x a b c)
    change scalarPartial _ p r = scalarPartial _ p r
    rw [he]
  have expanded : ehBoundaryDivergence g h p = ehSum3 (fun c a b =>
      (coordinateVolumeDensity g p * ((∑ d : Fin 4, Γ d c d) * B a b -
        (∑ d : Fin 4, Γ a c d * B d b) - (∑ d : Fin 4, Γ b c d * B a d)) * Z c a b +
          coordinateVolumeDensity g p * B a b * D c a b c) -
      (coordinateVolumeDensity g p * ((∑ d : Fin 4, Γ d c d) * B a c -
        (∑ d : Fin 4, Γ a c d * B d c) - (∑ d : Fin 4, Γ c c d * B a d)) * Z b a b +
          coordinateVolumeDensity g p * B a c * D b a b c)) := by
    simp only [ehBoundaryDivergence,ehSum3,
      eh_current_component_actual_partial g h hg hh p negative]
    simp_rw [eh_weighted_inverse_partial g sg hg p negative]
    simp only [ehWeightedInverse,Finset.sum_sub_distrib,B,Γ,Z,D]
  rw [expanded,eh_weighted_divergence_expansion_algebra,
    eh_palatini_derivative_contraction_algebra B D ds,
    eh_palatini_weighted_connection_algebra B Γ Z
      (leviCivita_torsion_free g sg p) (eh_lc_variation_lower_symmetric g h sg sh p)]
  simp_rw [eh_ricci_variation_is_palatini g h sg sh hg hh p (ne_of_lt negative)]
  simp only [ehSum3,ehSum4,ehConnectionRicciVariation,B,Γ,Z,D,
    mul_add,mul_sub,Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  ring

end
end AASCSemanticExhaustion
