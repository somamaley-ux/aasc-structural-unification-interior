import KGNRScalarDifferential
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Actual spatial rotations/translations, separately from internal comparison
arrows. Test covariance is proved by differentiation; the full graph square
then follows by a measure-preserving change of variables. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Filter LineDeriv Laplacian
open scoped SchwartzMap BigOperators Topology
namespace AASCKleinGordon

def kgNRRotateTest (R : KGSpatialSpace ≃ₗᵢ[ℝ] KGSpatialSpace) :
    𝓢(KGSpatialSpace,ℂ) →L[ℂ] 𝓢(KGSpatialSpace,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ R.toContinuousLinearEquiv

def kgNRTranslateTest (b : KGSpatialSpace) :
    𝓢(KGSpatialSpace,ℂ) →L[ℂ] 𝓢(KGSpatialSpace,ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (show (fun x : KGSpatialSpace => x+b).HasTemperateGrowth by fun_prop)
    (isometry_add_right b).antilipschitz

theorem kg_nr_rotate_test_laplacian (R : KGSpatialSpace ≃ₗᵢ[ℝ] KGSpatialSpace)
    (f : 𝓢(KGSpatialSpace,ℂ)) :
    kgSpatialLaplacian (kgNRRotateTest R f) = kgNRRotateTest R (kgSpatialLaplacian f) := by
  rw [← kg_spatial_schwartz_laplacian_intrinsic,← kg_spatial_schwartz_laplacian_intrinsic]
  rw [SchwartzMap.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 3) ℝ),
    SchwartzMap.laplacian_eq_sum ((EuclideanSpace.basisFun (Fin 3) ℝ).map R)]
  simp only [kgNRRotateTest,OrthonormalBasis.map_apply,
    SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv,map_sum]
  rfl

theorem kg_nr_translate_test_laplacian (b : KGSpatialSpace) (f : 𝓢(KGSpatialSpace,ℂ)) :
    kgSpatialLaplacian (kgNRTranslateTest b f) = kgNRTranslateTest b (kgSpatialLaplacian f) := by
  ext x
  rw [← kg_spatial_schwartz_laplacian_intrinsic,SchwartzMap.laplacian_apply]
  change (Δ (fun y => f (y+b))) x = kgSpatialLaplacian f (x+b)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp_rw [iteratedFDeriv_comp_add_right]
  rw [← congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (f : KGSpatialSpace → ℂ) (EuclideanSpace.basisFun (Fin 3) ℝ)) (x+b)]
  exact (SchwartzMap.laplacian_apply f (x+b)).symm.trans
    (congrArg (fun q : 𝓢(KGSpatialSpace,ℂ) => q (x+b)) (kg_spatial_schwartz_laplacian_intrinsic f))

theorem kg_nr_rotate_test_response (a : Parameters)
    (R : KGSpatialSpace ≃ₗᵢ[ℝ] KGSpatialSpace) (f : 𝓢(KGSpatialSpace,ℂ)) :
    kgNRSpatialTestResponse a (kgNRRotateTest R f) =
      kgNRRotateTest R (kgNRSpatialTestResponse a f) := by
  simp only [kgNRSpatialTestResponse,kg_nr_rotate_test_laplacian,map_smul]

theorem kg_nr_translate_test_response (a : Parameters) (b : KGSpatialSpace)
    (f : 𝓢(KGSpatialSpace,ℂ)) :
    kgNRSpatialTestResponse a (kgNRTranslateTest b f) =
      kgNRTranslateTest b (kgNRSpatialTestResponse a f) := by
  simp only [kgNRSpatialTestResponse,kg_nr_translate_test_laplacian,map_smul]

def kgNRSpatialPullback (e : KGSpatialSpace ≃ᵐ KGSpatialSpace)
    (he : MeasurePreserving e volume volume) : KGNRSpatialHilbert →ₗᵢ[ℂ] KGNRSpatialHilbert :=
  Lp.compMeasurePreservingₗᵢ ℂ e he

theorem kg_nr_spatial_pullback_distribution (e : KGSpatialSpace ≃ᵐ KGSpatialSpace)
    (he : MeasurePreserving e volume volume)
    (L : 𝓢(KGSpatialSpace,ℂ) →L[ℂ] 𝓢(KGSpatialSpace,ℂ))
    (hL : ∀ test x,L test x = test (e.symm x))
    (f : KGNRSpatialHilbert) (test : 𝓢(KGSpatialSpace,ℂ)) :
    ((kgNRSpatialPullback e he f : KGNRSpatialHilbert) : KGSpatialDistribution) test =
      (f : KGSpatialDistribution) (L test) := by
  simp only [Lp.toTemperedDistribution_apply,smul_eq_mul]
  calc
    _ = ∫ x, test x * f (e x) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_compMeasurePreserving f he] with x hx
      exact congrArg (fun z : ℂ => test x * z) hx
    _ = ∫ x, (L test) x * f x := by
      have h := he.integral_comp' (f := e) (fun y => test (e.symm y) * f y)
      simpa only [MeasurableEquiv.symm_apply_apply,hL] using h

theorem kg_nr_spatial_pullback_graph (a : Parameters)
    (e : KGSpatialSpace ≃ᵐ KGSpatialSpace) (he : MeasurePreserving e volume volume)
    (L : 𝓢(KGSpatialSpace,ℂ) →L[ℂ] 𝓢(KGSpatialSpace,ℂ))
    (hL : ∀ test x,L test x = test (e.symm x))
    (hP : ∀ test,kgNRSpatialTestResponse a (L test) = L (kgNRSpatialTestResponse a test))
    (f g : KGNRSpatialHilbert) (hg : (f,g) ∈ (kgNRSpatialKinetic a).graph) :
    (kgNRSpatialPullback e he f,kgNRSpatialPullback e he g) ∈ (kgNRSpatialKinetic a).graph := by
  apply (kg_nr_spatial_kinetic_test_graph a _ _).mpr
  intro test
  rw [kg_nr_spatial_pullback_distribution e he L hL,
    (kg_nr_spatial_kinetic_test_graph a f g).mp hg (L test),hP,
    kg_nr_spatial_pullback_distribution e he L hL]

def kgNRSpatialRotation (R : KGSpatialSpace ≃ₗᵢ[ℝ] KGSpatialSpace) :
    KGNRSpatialHilbert →ₗᵢ[ℂ] KGNRSpatialHilbert :=
  kgNRSpatialPullback R.toMeasurableEquiv R.measurePreserving

def kgNRSpatialTranslation (b : KGSpatialSpace) :
    KGNRSpatialHilbert →ₗᵢ[ℂ] KGNRSpatialHilbert :=
  kgNRSpatialPullback (MeasurableEquiv.addRight b) (measurePreserving_add_right volume b)

theorem kg_nr_spatial_rotation_graph (a : Parameters)
    (R : KGSpatialSpace ≃ₗᵢ[ℝ] KGSpatialSpace) (f g : KGNRSpatialHilbert)
    (h : (f,g) ∈ (kgNRSpatialKinetic a).graph) :
    (kgNRSpatialRotation R f,kgNRSpatialRotation R g) ∈ (kgNRSpatialKinetic a).graph :=
  kg_nr_spatial_pullback_graph a R.toMeasurableEquiv R.measurePreserving
    (kgNRRotateTest R.symm) (fun _ _ => rfl) (kg_nr_rotate_test_response a R.symm) f g h

theorem kg_nr_spatial_translation_graph (a : Parameters) (b : KGSpatialSpace)
    (f g : KGNRSpatialHilbert) (h : (f,g) ∈ (kgNRSpatialKinetic a).graph) :
    (kgNRSpatialTranslation b f,kgNRSpatialTranslation b g) ∈ (kgNRSpatialKinetic a).graph :=
  kg_nr_spatial_pullback_graph a (MeasurableEquiv.addRight b) (measurePreserving_add_right volume b)
    (kgNRTranslateTest (-b)) (fun _ _ => by simp [kgNRTranslateTest])
    (kg_nr_translate_test_response a (-b)) f g h

end AASCKleinGordon
