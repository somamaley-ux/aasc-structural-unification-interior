import KGConeCutoffSupport
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
set_option maxHeartbeats 800000
open Set MeasureTheory
namespace AASCKleinGordon

def kgSpatialDirection (i : Fin 3) : KGSpatialSpace := EuclideanSpace.single i 1

def kgSpatialDivergence (J : KGSpatialSpace → KGSpatialSpace) (x : KGSpatialSpace) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun y => J y i) x (kgSpatialDirection i)

theorem spatial_inner_eq_sum (v w : KGSpatialSpace) :
    inner ℝ v w = ∑ i : Fin 3, v i*w i := by
  simp [PiLp.inner_apply,mul_comm]

/-- Actual Haar integration by parts for the concrete smooth cone cutoff. -/
theorem smoothConeCutoff_integral_divergence
    (δ R t : ℝ) (x₀ : KGSpatialSpace) (hδ : 0 < δ)
    (J : KGSpatialSpace → KGSpatialSpace) (hJ : Continuous J)
    (hJd : ∀ i : Fin 3, Differentiable ℝ (fun x => J x i))
    (hDJ : ∀ i : Fin 3, Continuous
      (fun x => fderiv ℝ (fun y => J y i) x (kgSpatialDirection i))) :
    (∫ x, smoothConeCutoff δ R t x₀ x*kgSpatialDivergence J x) =
      -(∫ x, inner ℝ (smoothConeCutoffGradient δ R t x₀ x) (J x)) := by
  let χ := smoothConeCutoff δ R t x₀
  let ξ := smoothConeCutoffGradient δ R t x₀
  have hc : Continuous χ := (smoothConeCutoff_joint_contDiff δ R x₀ hδ).continuous.comp
    (continuous_const.prodMk continuous_id)
  have hg : Continuous ξ := (smoothConeCutoffGradient_joint_continuous δ R x₀ hδ).comp
    (continuous_const.prodMk continuous_id)
  have hχ : HasCompactSupport χ := smoothConeCutoff_hasCompactSupport δ R t x₀
  have hξ (i : Fin 3) : HasCompactSupport (fun x => ξ x i) :=
    compactSupport_of_zero_outside_compact (isCompact_closedBall x₀ (R-t)) (fun x hx => by
      have hh := (smoothConeCutoff_uniform_support δ R t t t x₀ x ⟨le_rfl,le_rfl⟩ hx).2.2
      change smoothConeCutoffGradient δ R t x₀ x i=0
      rw [hh]
      rfl)
  have hJi (i : Fin 3) : Continuous (fun x => J x i) := (hJd i).continuous
  have hξi (i : Fin 3) : Continuous (fun x => ξ x i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp hg
  have hi (i : Fin 3) : Integrable (fun x => χ x*fderiv ℝ (fun y => J y i) x (kgSpatialDirection i)) :=
    (hc.mul (hDJ i)).integrable_of_hasCompactSupport (hχ.mul_right)
  have hgi (i : Fin 3) : Integrable (fun x => ξ x i*J x i) :=
    ((hξi i).mul (hJi i)).integrable_of_hasCompactSupport ((hξ i).mul_right)
  have hdf (x : KGSpatialSpace) (i : Fin 3) : fderiv ℝ χ x (kgSpatialDirection i)=ξ x i := by
    rw [(smoothConeCutoff_hasFDerivAt δ R t x₀ x hδ).fderiv]
    simp [innerSL_apply_apply,kgSpatialDirection,EuclideanSpace.inner_single_right,ξ]
  have hibp (i : Fin 3) :
      (∫ x, χ x*fderiv ℝ (fun y => J y i) x (kgSpatialDirection i)) = -(∫ x, ξ x i*J x i) := by
    have hgi' : Integrable (fun x => fderiv ℝ χ x (kgSpatialDirection i)*J x i) := by
      simpa only [hdf] using hgi i
    have hp : Integrable (fun x => χ x*J x i) :=
      (hc.mul (hJi i)).integrable_of_hasCompactSupport hχ.mul_right
    simpa only [hdf] using integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      hgi' (hi i) hp (fun x => (smoothConeCutoff_hasFDerivAt δ R t x₀ x hδ).differentiableAt) (hJd i)
  calc
    _ = ∫ x, ∑ i : Fin 3, χ x*fderiv ℝ (fun y => J y i) x (kgSpatialDirection i) := by
      congr 1
      funext x
      simp [kgSpatialDivergence,Finset.mul_sum,χ]
    _ = ∑ i : Fin 3, ∫ x, χ x*fderiv ℝ (fun y => J y i) x (kgSpatialDirection i) :=
      integral_finset_sum _ (fun i _ => hi i)
    _ = ∑ i : Fin 3, -(∫ x, ξ x i*J x i) := Finset.sum_congr rfl (fun i _ => hibp i)
    _ = -(∫ x, inner ℝ (ξ x) (J x)) := by
      rw [Finset.sum_neg_distrib,← integral_finset_sum _ (fun i _ => hgi i)]
      simp only [spatial_inner_eq_sum]

end AASCKleinGordon
