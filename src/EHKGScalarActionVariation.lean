import EHKGIntegratedActionIdentity

/-! Ordinary field variation of the actual inherited scalar action on a
compact subdomain. The derivative is constructed from its quadratic density,
not supplied as an action/operator agreement certificate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open scoped Topology BigOperators
namespace AASCKleinGordon.CurvedKG

theorem native_scalar_density_quadratic (G : NativeRealMatrix) (v w : Fin 4 → ℝ)
    (phi psi mu2 s : ℝ) :
    nativeRealClockDensity G (fun i => v i + s * w i) (phi + s * psi) mu2 =
      nativeRealClockDensity G v phi mu2 +
        s * (nativeRealClockDensity G (fun i => v i + w i) (phi + psi) mu2 -
          nativeRealClockDensity G v phi mu2 - nativeRealClockDensity G w psi mu2) +
        s ^ 2 * nativeRealClockDensity G w psi mu2 := by
  simp only [nativeRealClockDensity, Fin.sum_univ_four]
  ring

theorem scalar_partial_add_real_multiple (u d : CoordinatePoint → ℝ)
    (regularU : ContDiff ℝ (⊤ : ℕ∞) u) (regularD : ContDiff ℝ (⊤ : ℕ∞) d)
    (s : ℝ) (p : CoordinatePoint) (i : Fin 4) :
    scalarPartial (fun q => u q + s * d q) p i = scalarPartial u p i + s * scalarPartial d p i := by
  have first := (regularU.differentiable (by simp) p).hasFDerivAt.add
    ((regularD.differentiable (by simp) p).hasFDerivAt.const_mul s)
  have actual := first.fderiv
  change fderiv ℝ (fun q => u q + s * d q) p = _ at actual
  rw [scalarPartial, actual]
  simp [scalarPartial]

theorem same_eh_density_quadratic (a : Parameters) (u d : CoordinatePoint → ℝ)
    (regularU : ContDiff ℝ (⊤ : ℕ∞) u) (regularD : ContDiff ℝ (⊤ : ℕ∞) d)
    (s : ℝ) (p : CoordinatePoint) :
    sameEHScalarDensity a (fun q => u q + s * d q) p =
      sameEHScalarDensity a u p +
        s * (sameEHScalarDensity a (fun q => u q + d q) p -
          sameEHScalarDensity a u p - sameEHScalarDensity a d p) +
        s ^ 2 * sameEHScalarDensity a d p := by
  have first : scalarPartial (fun q => u q + s * d q) p =
      (fun i => scalarPartial u p i + s * scalarPartial d p i) := by
    funext i
    exact scalar_partial_add_real_multiple u d regularU regularD s p i
  have sumFirst : scalarPartial (fun q => u q + d q) p =
      (fun i => scalarPartial u p i + scalarPartial d p i) := by
    funext i
    simpa using scalar_partial_add_real_multiple u d regularU regularD 1 p i
  simp only [sameEHScalarDensity, first, sumFirst]
  exact native_scalar_density_quadratic _ _ _ _ _ _ _

def sameEHScalarActionOn (a : Parameters) (K : Compacts CoordinatePoint)
    (u : CoordinatePoint → ℝ) : ℝ := ∫ p in (K : Set CoordinatePoint), sameEHScalarDensity a u p

def sameEHScalarActionLinearVariationOn (a : Parameters) (K : Compacts CoordinatePoint)
    (u d : CoordinatePoint → ℝ) : ℝ :=
  sameEHScalarActionOn a K (fun q => u q + d q) - sameEHScalarActionOn a K u - sameEHScalarActionOn a K d

theorem same_eh_action_quadratic (a : Parameters) (K : Compacts CoordinatePoint)
    (inside : (K : Set CoordinatePoint) ⊆ protectedDiamond (conformalFrequency a))
    (u d : CoordinatePoint → ℝ) (regularU : ContDiff ℝ (⊤ : ℕ∞) u)
    (regularD : ContDiff ℝ (⊤ : ℕ∞) d) (s : ℝ) :
    sameEHScalarActionOn a K (fun q => u q + s * d q) =
      sameEHScalarActionOn a K u + s * sameEHScalarActionLinearVariationOn a K u d +
        s ^ 2 * sameEHScalarActionOn a K d := by
  have integrableU : IntegrableOn (sameEHScalarDensity a u) (K : Set CoordinatePoint) :=
    ContinuousOn.integrableOn_compact K.isCompact
      ((same_eh_scalar_density_continuous a u regularU.contDiffOn).mono inside)
  have integrableD : IntegrableOn (sameEHScalarDensity a d) (K : Set CoordinatePoint) :=
    ContinuousOn.integrableOn_compact K.isCompact
      ((same_eh_scalar_density_continuous a d regularD.contDiffOn).mono inside)
  have integrableSum : IntegrableOn (sameEHScalarDensity a (fun q => u q + d q)) (K : Set CoordinatePoint) :=
    ContinuousOn.integrableOn_compact K.isCompact
      ((same_eh_scalar_density_continuous a _ (regularU.add regularD).contDiffOn).mono inside)
  unfold sameEHScalarActionLinearVariationOn sameEHScalarActionOn
  have pointwise := same_eh_density_quadratic a u d regularU regularD s
  simp_rw [pointwise]
  have outerSplit : (∫ p in (K : Set CoordinatePoint),
      sameEHScalarDensity a u p + s * (sameEHScalarDensity a (fun q => u q + d q) p -
        sameEHScalarDensity a u p - sameEHScalarDensity a d p) + s ^ 2 * sameEHScalarDensity a d p) =
      (∫ p in (K : Set CoordinatePoint), sameEHScalarDensity a u p +
        s * (sameEHScalarDensity a (fun q => u q + d q) p - sameEHScalarDensity a u p - sameEHScalarDensity a d p)) +
      ∫ p in (K : Set CoordinatePoint), s ^ 2 * sameEHScalarDensity a d p :=
    integral_add (integrableU.add ((integrableSum.sub integrableU |>.sub integrableD).const_mul s))
      (integrableD.const_mul (s ^ 2))
  have innerSplit : (∫ p in (K : Set CoordinatePoint), sameEHScalarDensity a u p +
      s * (sameEHScalarDensity a (fun q => u q + d q) p - sameEHScalarDensity a u p - sameEHScalarDensity a d p)) =
      (∫ p in (K : Set CoordinatePoint), sameEHScalarDensity a u p) +
      ∫ p in (K : Set CoordinatePoint), s * (sameEHScalarDensity a (fun q => u q + d q) p -
        sameEHScalarDensity a u p - sameEHScalarDensity a d p) :=
    integral_add integrableU ((integrableSum.sub integrableU |>.sub integrableD).const_mul s)
  have differenceSplit : (∫ p in (K : Set CoordinatePoint), sameEHScalarDensity a (fun q => u q + d q) p -
      sameEHScalarDensity a u p - sameEHScalarDensity a d p) =
      (∫ p in (K : Set CoordinatePoint), sameEHScalarDensity a (fun q => u q + d q) p) -
      (∫ p in (K : Set CoordinatePoint), sameEHScalarDensity a u p) -
      ∫ p in (K : Set CoordinatePoint), sameEHScalarDensity a d p := by
    have firstSplit : (∫ p in (K : Set CoordinatePoint), sameEHScalarDensity a (fun q => u q + d q) p -
        sameEHScalarDensity a u p - sameEHScalarDensity a d p) =
        (∫ p in (K : Set CoordinatePoint), sameEHScalarDensity a (fun q => u q + d q) p - sameEHScalarDensity a u p) -
        ∫ p in (K : Set CoordinatePoint), sameEHScalarDensity a d p :=
      integral_sub (integrableSum.sub integrableU) integrableD
    rw [firstSplit, integral_sub integrableSum integrableU]
  rw [outerSplit, innerSplit, integral_const_mul, differenceSplit, integral_const_mul]

theorem same_eh_scalar_action_field_hasDerivAt (a : Parameters) (K : Compacts CoordinatePoint)
    (inside : (K : Set CoordinatePoint) ⊆ protectedDiamond (conformalFrequency a))
    (u d : CoordinatePoint → ℝ) (regularU : ContDiff ℝ (⊤ : ℕ∞) u)
    (regularD : ContDiff ℝ (⊤ : ℕ∞) d) :
    HasDerivAt (fun s : ℝ => sameEHScalarActionOn a K (fun q => u q + s * d q))
      (sameEHScalarActionLinearVariationOn a K u d) 0 := by
  have polynomial := ((hasDerivAt_const (0 : ℝ) (sameEHScalarActionOn a K u)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (sameEHScalarActionLinearVariationOn a K u d))).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (sameEHScalarActionOn a K d))
  have equality : (fun s : ℝ => sameEHScalarActionOn a K (fun q => u q + s * d q)) =
      (fun s : ℝ => sameEHScalarActionOn a K u + s * sameEHScalarActionLinearVariationOn a K u d +
        s ^ 2 * sameEHScalarActionOn a K d) := by
    funext s
    exact same_eh_action_quadratic a K inside u d regularU regularD s
  rw [equality]
  simpa using polynomial

end AASCKleinGordon.CurvedKG
