import KGPhysicalSpatialUnitary
import KGSpatialCauchyDifferential

/-! The independent distributional Laplacian and its Fourier symbol.
The weak operator is defined by actual test-function differentiation, before
comparison with an L2 multiplier. No maximal-domain certificate is an input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Filter LineDeriv Laplacian
open scoped SchwartzMap FourierTransform BigOperators ContDiff
namespace AASCKleinGordon

abbrev KGSpatialDistribution := 𝓢'(KGSpatialSpace, ℂ)

def kgSpatialDistributionLaplacian (T : KGSpatialDistribution) : KGSpatialDistribution :=
  Δ T

theorem kg_spatial_schwartz_laplacian_intrinsic (f : 𝓢(KGSpatialSpace, ℂ)) :
    Δ f = kgSpatialLaplacian f := by
  rw [SchwartzMap.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only [EuclideanSpace.basisFun_apply, kgSpatialLaplacian, kgSpatialPartialCLM,
    kgSpatialDirection, lineDerivOpCLM_apply]

theorem kg_spatial_distribution_laplacian_test (T : KGSpatialDistribution)
    (f : 𝓢(KGSpatialSpace, ℂ)) :
    kgSpatialDistributionLaplacian T f = T (kgSpatialLaplacian f) := by
  rw [kgSpatialDistributionLaplacian, TemperedDistribution.laplacian_apply_apply,
    kg_spatial_schwartz_laplacian_intrinsic]

theorem kg_spatial_distribution_laplacian_sum (T : KGSpatialDistribution) :
    kgSpatialDistributionLaplacian T =
      ∑ i : Fin 3, ∂_{kgSpatialDirection i} (∂_{kgSpatialDirection i} T) := by
  rw [kgSpatialDistributionLaplacian,
    TemperedDistribution.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only [EuclideanSpace.basisFun_apply, kgSpatialDirection]

def kgSpatialCoordinateSymbol (i : Fin 3) (x : KGSpatialSpace) : ℂ := (x i : ℂ)

theorem kg_spatial_coordinate_symbol_temperate (i : Fin 3) :
    (kgSpatialCoordinateSymbol i).HasTemperateGrowth := by
  have h : (fun x : KGSpatialSpace =>
      ((inner ℝ x (kgSpatialDirection i) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  convert h using 1
  funext x
  simp [kgSpatialDirection, EuclideanSpace.inner_single_right, kgSpatialCoordinateSymbol]

theorem kg_spatial_coordinate_inner (i : Fin 3) (x : KGSpatialSpace) :
    ((inner ℝ x (kgSpatialDirection i) : ℝ) : ℂ) = kgSpatialCoordinateSymbol i x := by
  simp [kgSpatialDirection, EuclideanSpace.inner_single_right, kgSpatialCoordinateSymbol]

theorem kg_spatial_distribution_partial_fourier (i : Fin 3) (T : KGSpatialDistribution) :
    𝓕 (∂_{kgSpatialDirection i} T) =
      (2 * Real.pi * Complex.I) •
        TemperedDistribution.smulLeftCLM ℂ (kgSpatialCoordinateSymbol i) (𝓕 T) := by
  rw [TemperedDistribution.fourier_lineDerivOp_eq]
  have hc : (fun x : KGSpatialSpace => ((inner ℝ x (kgSpatialDirection i) : ℝ) : ℂ)) =
      kgSpatialCoordinateSymbol i := funext (kg_spatial_coordinate_inner i)
  rw [hc]

def kgSpatialLaplacianSymbol (x : KGSpatialSpace) : ℂ :=
  ∑ i : Fin 3, -(((2 * Real.pi * x i : ℝ) : ℂ) ^ 2)

theorem kg_spatial_laplacian_symbol_temperate :
    kgSpatialLaplacianSymbol.HasTemperateGrowth := by
  have h : (fun x : KGSpatialSpace => ∑ i : Fin 3,
      -((2 * (Real.pi : ℂ) * kgSpatialCoordinateSymbol i x) ^ 2)).HasTemperateGrowth := by
    apply Function.HasTemperateGrowth.sum
    intro i _
    have hi := kg_spatial_coordinate_symbol_temperate i
    fun_prop
  convert h using 1
  funext x
  simp only [kgSpatialLaplacianSymbol,kgSpatialCoordinateSymbol]
  push_cast
  rfl

theorem kg_spatial_laplacian_symbol_value (x : KGSpatialSpace) :
    kgSpatialLaplacianSymbol x = -(((2 * Real.pi) ^ 2 * ‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [kgSpatialLaplacianSymbol, Fin.sum_univ_succ, Finset.univ_unique,
    Finset.sum_singleton, Real.norm_eq_abs, sq_abs]
  push_cast
  ring

theorem kg_spatial_distribution_second_partial_fourier (i : Fin 3)
    (T : KGSpatialDistribution) :
    𝓕 (∂_{kgSpatialDirection i} (∂_{kgSpatialDirection i} T)) =
      TemperedDistribution.smulLeftCLM ℂ
        (fun x : KGSpatialSpace => -(((2 * Real.pi * x i : ℝ) : ℂ) ^ 2)) (𝓕 T) := by
  rw [kg_spatial_distribution_partial_fourier, kg_spatial_distribution_partial_fourier,
    map_smul, smul_smul,
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
      (kg_spatial_coordinate_symbol_temperate i) (kg_spatial_coordinate_symbol_temperate i)]
  have hs : (fun x : KGSpatialSpace => -(((2 * Real.pi * x i : ℝ) : ℂ) ^ 2)) =
      (2 * Real.pi * Complex.I * (2 * Real.pi * Complex.I)) •
        (kgSpatialCoordinateSymbol i * kgSpatialCoordinateSymbol i) := by
    funext x
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, kgSpatialCoordinateSymbol]
    push_cast
    linear_combination (-((2 * (Real.pi : ℂ) * x i) ^ 2)) * Complex.I_sq
  rw [hs, TemperedDistribution.smulLeftCLM_smul
    ((kg_spatial_coordinate_symbol_temperate i).mul (kg_spatial_coordinate_symbol_temperate i))]
  rfl

theorem kg_spatial_distribution_laplacian_fourier (T : KGSpatialDistribution) :
    𝓕 (kgSpatialDistributionLaplacian T) =
      TemperedDistribution.smulLeftCLM ℂ kgSpatialLaplacianSymbol (𝓕 T) := by
  rw [kg_spatial_distribution_laplacian_sum, FourierTransform.fourier_sum]
  simp_rw [kg_spatial_distribution_second_partial_fourier]
  change (∑ i : Fin 3, TemperedDistribution.smulLeftCLM ℂ
      (fun x : KGSpatialSpace => -(((2 * Real.pi * x i : ℝ) : ℂ) ^ 2)) (𝓕 T)) =
    TemperedDistribution.smulLeftCLM ℂ
      (fun x : KGSpatialSpace => ∑ i : Fin 3, -(((2 * Real.pi * x i : ℝ) : ℂ) ^ 2)) (𝓕 T)
  have hg : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      (fun x : KGSpatialSpace => -(((2 * Real.pi * x i : ℝ) : ℂ) ^ 2)).HasTemperateGrowth := by
    intro i _
    have hi := kg_spatial_coordinate_symbol_temperate i
    have ht : (fun x : KGSpatialSpace =>
        -((2 * (Real.pi : ℂ) * kgSpatialCoordinateSymbol i x) ^ 2)).HasTemperateGrowth := by fun_prop
    convert ht using 1
    funext x
    simp only [kgSpatialCoordinateSymbol]
    push_cast
    rfl
  rw [TemperedDistribution.smulLeftCLM_sum hg]
  simp only [ContinuousLinearMap.sum_apply]

theorem kg_spatial_continuous_multiplier_locally_integrable
    (v : KGSpatialSpace → ℂ) (hv : Continuous v) (f : KGNRSpatialHilbert) :
    LocallyIntegrable (fun x => v x * f x) volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  exact IntegrableOn.continuousOn_mul hv.continuousOn
    (((Lp.memLp f).locallyIntegrable (by norm_num)).integrableOn_isCompact hK) hK

theorem kg_spatial_distribution_multiplier_eq_iff
    (v : KGSpatialSpace → ℂ) (hv : v.HasTemperateGrowth)
    (f g : KGNRSpatialHilbert) :
    (g : KGSpatialDistribution) = TemperedDistribution.smulLeftCLM ℂ v f ↔
      g =ᵐ[volume] (fun x => v x * f x) := by
  constructor
  · intro h
    apply ae_eq_of_integral_contDiff_smul_eq
      ((Lp.memLp g).locallyIntegrable (by norm_num))
      (kg_spatial_continuous_multiplier_locally_integrable v hv.1.continuous f)
    intro q hq hqc
    have hqc' : HasCompactSupport (Complex.ofRealCLM ∘ q) := hqc.comp_left rfl
    have hq' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ q) := by fun_prop
    let test : 𝓢(KGSpatialSpace, ℂ) := hqc'.toSchwartzMap hq'
    have ht := congrArg (fun T : KGSpatialDistribution => T test) h
    simp only [Lp.toTemperedDistribution_apply,
      TemperedDistribution.smulLeftCLM_apply_apply,
      SchwartzMap.smulLeftCLM_apply_apply hv, smul_eq_mul] at ht
    change (∫ x, (q x : ℂ) * g x) = ∫ x, (v x * (q x : ℂ)) * f x at ht
    simp only [Complex.real_smul]
    calc
      _ = _ := ht
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by ring)
  · intro h
    ext test
    simp only [Lp.toTemperedDistribution_apply,
      TemperedDistribution.smulLeftCLM_apply_apply,
      SchwartzMap.smulLeftCLM_apply_apply hv, smul_eq_mul]
    apply integral_congr_ae
    filter_upwards [h] with x hx
    rw [hx]
    ring

end AASCKleinGordon
