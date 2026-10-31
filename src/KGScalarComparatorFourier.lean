import KGScalarFreeComparator

/-! The comparator's canonical polynomial Fourier symbol is proved to
represent its complete distribution graph. Calibration is a declared inertial
spectral datum, never point evaluation of an L2 state or a desired H identity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory
open scoped SchwartzMap FourierTransform BigOperators
namespace AASCKleinGordon

def kgScalarPrincipalFourierSymbol (D : KGScalarDifferentialData) (ξ : KGSpatialSpace) : ℂ :=
  ∑ i : Fin 3,∑ j : Fin 3,D.principal 0 i j *
    (-(((2*Real.pi*ξ i)*(2*Real.pi*ξ j) : ℝ) : ℂ))

theorem kg_scalar_principal_fourier_symbol_of_uniform
    (D : KGScalarDifferentialData) (c : ℝ)
    (principal : ∀ x i j,D.principal x i j = if i=j then (c : ℂ) else 0)
    (ξ : KGSpatialSpace) :
    kgScalarPrincipalFourierSymbol D ξ = (c : ℂ)*kgSpatialLaplacianSymbol ξ := by
  unfold kgScalarPrincipalFourierSymbol kgSpatialLaplacianSymbol
  simp_rw [principal]
  simp only [ite_mul,zero_mul]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

theorem kg_free_comparator_symbol_temperate
    {H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert} (C : KGScalarFreeComparator H) :
    (kgScalarPrincipalFourierSymbol C.data).HasTemperateGrowth := by
  obtain ⟨c,_,hp⟩ := C.uniform_principal
  have h := (Function.HasTemperateGrowth.const (c : ℂ)).mul kg_spatial_laplacian_symbol_temperate
  convert h using 1
  funext ξ
  exact kg_scalar_principal_fourier_symbol_of_uniform C.data c hp ξ

theorem kg_free_comparator_complete_fourier_graph
    {H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert} (C : KGScalarFreeComparator H)
    (f g : KGNRSpatialHilbert) :
    (f,g) ∈ H.graph ↔
      ((𝓕 g : KGNRSpatialHilbert) : KGSpatialDistribution) =
        TemperedDistribution.smulLeftCLM ℂ (kgScalarPrincipalFourierSymbol C.data)
          ((𝓕 f : KGNRSpatialHilbert) : KGSpatialDistribution) := by
  obtain ⟨c,_,hp⟩ := C.uniform_principal
  have hs : kgScalarPrincipalFourierSymbol C.data = (c : ℂ) • kgSpatialLaplacianSymbol :=
    funext (kg_scalar_principal_fourier_symbol_of_uniform C.data c hp)
  rw [kg_free_comparator_graph_of_principal C c hp,hs,
    TemperedDistribution.smulLeftCLM_smul kg_spatial_laplacian_symbol_temperate]
  simp only [ContinuousLinearMap.smul_apply]
  rw [← Lp.fourier_toTemperedDistribution_eq,← Lp.fourier_toTemperedDistribution_eq,
    ← kg_spatial_distribution_laplacian_fourier,← FourierTransform.fourier_smul]
  constructor
  · exact congrArg (fun T : KGSpatialDistribution => 𝓕 T)
  · intro h
    have hi := congrArg (fun T : KGSpatialDistribution => 𝓕⁻ T) h
    simpa only [FourierTransform.fourierInv_fourier_eq] using hi

def kgScalarPrincipalRealSymbol (D : KGScalarDifferentialData) (ξ : KGSpatialSpace) : ℝ :=
  (kgScalarPrincipalFourierSymbol D ξ).re

theorem kg_free_comparator_symbol_real
    {H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert} (C : KGScalarFreeComparator H)
    (ξ : KGSpatialSpace) :
    kgScalarPrincipalFourierSymbol C.data ξ = (kgScalarPrincipalRealSymbol C.data ξ : ℂ) := by
  obtain ⟨c,_,hp⟩ := C.uniform_principal
  have he : kgScalarPrincipalFourierSymbol C.data ξ =
      ((c * -((2*Real.pi)^2*‖ξ‖^2) : ℝ) : ℂ) := by
    rw [kg_scalar_principal_fourier_symbol_of_uniform C.data c hp,
      kg_spatial_laplacian_symbol_value]
    push_cast
    rfl
  unfold kgScalarPrincipalRealSymbol
  rw [he]
  simp only [Complex.ofReal_re]

theorem kg_free_comparator_fourier_multiplier_graph
    {H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert} (C : KGScalarFreeComparator H)
    (f g : KGNRSpatialHilbert) :
    (f,g) ∈ H.graph ↔ (𝓕 f,𝓕 g) ∈
      (Multiplication.realMultiplication (kgScalarPrincipalRealSymbol C.data)).graph := by
  rw [kg_free_comparator_complete_fourier_graph C,
    kg_spatial_distribution_multiplier_eq_iff _ (kg_free_comparator_symbol_temperate C),
    Multiplication.realMultiplication_mem_graph]
  simp_rw [kg_free_comparator_symbol_real C]

theorem kg_free_comparator_exact_multiplier_domain
    {H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert} (C : KGScalarFreeComparator H)
    (f : KGNRSpatialHilbert) :
    f ∈ H.domain ↔ MemLp
      (fun ξ => (kgScalarPrincipalRealSymbol C.data ξ : ℂ)*(𝓕 f) ξ) 2 volume := by
  rw [← Multiplication.realMultiplication_exact_domain]
  constructor
  · intro h
    exact LinearPMap.mem_domain_of_mem_graph
      ((kg_free_comparator_fourier_multiplier_graph C f _).mp (H.mem_graph ⟨f,h⟩))
  · intro h
    let T : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert :=
      Multiplication.realMultiplication (kgScalarPrincipalRealSymbol C.data)
    have hg := T.mem_graph ⟨𝓕 f,h⟩
    have hi : (𝓕 f,𝓕 (𝓕⁻ (T ⟨𝓕 f,h⟩))) ∈ T.graph := by
      simpa only [FourierTransform.fourier_fourierInv_eq] using hg
    exact LinearPMap.mem_domain_of_mem_graph
      ((kg_free_comparator_fourier_multiplier_graph C f _).mpr hi)

def kgScalarCalibrationFrequency : KGSpatialSpace := kgSpatialDirection 0

theorem kg_scalar_calibration_frequency_nonzero : kgScalarCalibrationFrequency ≠ 0 := by
  intro h
  have he := congrArg (fun ξ : KGSpatialSpace => ξ (0 : Fin 3)) h
  simp [kgScalarCalibrationFrequency,kgSpatialDirection] at he

/-- One admitted value of the CONTINUOUS POLYNOMIAL dispersion symbol.
This is an explicit physical anchor input, not derived from positivity alone. -/
def KGFreeAnchoredDispersionAt (a : Parameters)
    {H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert} (C : KGScalarFreeComparator H) : Prop :=
  kgScalarPrincipalFourierSymbol C.data kgScalarCalibrationFrequency =
    (kgNRFrequencyKineticEnergy a kgScalarCalibrationFrequency : ℂ)

/-- The full free dispersion ledger of the source; one nonzero frequency
suffices only after the uniform one-parameter normal form is proved. -/
def KGFreeInertialDispersion (a : Parameters)
    {H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert} (C : KGScalarFreeComparator H) : Prop :=
  ∀ ξ,kgScalarPrincipalFourierSymbol C.data ξ = (kgNRFrequencyKineticEnergy a ξ : ℂ)

theorem kg_free_anchored_coefficient
    (a : Parameters) {H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert}
    (C : KGScalarFreeComparator H) (c : ℝ)
    (principal : ∀ x i j,C.data.principal x i j = if i=j then (c : ℂ) else 0)
    (calibration : KGFreeAnchoredDispersionAt a C) : c = kgNRPrincipalCoefficient a := by
  have hc := calibration
  change kgScalarPrincipalFourierSymbol C.data kgScalarCalibrationFrequency = _ at hc
  rw [kg_scalar_principal_fourier_symbol_of_uniform C.data c principal,
    kg_spatial_laplacian_symbol_value,kg_nr_frequency_kinetic_symbol] at hc
  let q : ℝ := (2*Real.pi)^2 * ‖kgScalarCalibrationFrequency‖^2
  have hq : q ≠ 0 := mul_ne_zero
    (pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero))
    (pow_ne_zero _ (norm_ne_zero_iff.mpr kg_scalar_calibration_frequency_nonzero))
  have hr : c * -q = (a.hbar^2/(2*a.mass))*q := by exact_mod_cast hc
  have hn : -c = a.hbar^2/(2*a.mass) := mul_right_cancel₀ hq (by nlinarith only [hr])
  unfold kgNRPrincipalCoefficient
  linarith

theorem kg_free_calibrated_comparator_eq
    (a : Parameters) {H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert}
    (C : KGScalarFreeComparator H) (calibration : KGFreeAnchoredDispersionAt a C) :
    H = kgNRSpatialKinetic a := by
  obtain ⟨c,_,hp⟩ := C.uniform_principal
  have hc := kg_free_anchored_coefficient a C c hp calibration
  have hz : (c : ℂ) = (-(a.hbar^2/(2*a.mass)) : ℂ) := by
    rw [hc,kgNRPrincipalCoefficient]
    push_cast
    rfl
  apply LinearPMap.eq_of_eq_graph
  ext ⟨f,g⟩
  rw [kg_free_comparator_graph_of_principal C c hp,kg_nr_spatial_kinetic_weak_graph]
  unfold kgSpatialWeakKineticGraph
  rw [hz]

def kgNRFreeComparator (a : Parameters) : KGScalarFreeComparator (kgNRSpatialKinetic a) :=
  kgScalarFreeComparatorOfSSQ1 a (kgNRFreeSSQ1Witness a)

theorem kg_nr_free_comparator_inertial_dispersion (a : Parameters) :
    KGFreeInertialDispersion a (kgNRFreeComparator a) := by
  intro ξ
  rw [kg_scalar_principal_fourier_symbol_of_uniform _ (kgNRPrincipalCoefficient a)
    (fun _ _ _ => rfl),kg_spatial_laplacian_symbol_value,kg_nr_frequency_kinetic_symbol]
  unfold kgNRPrincipalCoefficient
  push_cast
  ring

end AASCKleinGordon
