import SKGSpatialCalculus

/-! The spatial Euler expression is the actual derivative of the compact
relative Hamiltonian integral, with momentum held fixed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

def spatialHamiltonianDensity (L U pi : KGSpatialSpace → ℝ) (mu2 : ℝ) (x : KGSpatialSpace) : ℝ :=
  scalarCanonicalHamiltonian (L x) mu2 (U x) (pi x) (spatialPartial U x)

def spatialHamiltonianRelative (L U pi d : KGSpatialSpace → ℝ) (mu2 t : ℝ) : ℝ :=
  ∫ x : KGSpatialSpace, spatialHamiltonianDensity L (fun y => U y + t * d y) pi mu2 x -
    spatialHamiltonianDensity L U pi mu2 x

def spatialHamiltonianFirst (L U d : KGSpatialSpace → ℝ) (mu2 : ℝ) (x : KGSpatialSpace) : ℝ :=
  mu2 * L x ^ 2 * U x * d x + ∑ i : Fin 3, L x * spatialPartial U x i * spatialPartial d x i

def spatialHamiltonianSecond (L d : KGSpatialSpace → ℝ) (mu2 : ℝ) (x : KGSpatialSpace) : ℝ :=
  (1 / 2 : ℝ) * (mu2 * L x ^ 2 * d x * d x +
    ∑ i : Fin 3, L x * spatialPartial d x i * spatialPartial d x i)

def spatialHamiltonianEuler (L U : KGSpatialSpace → ℝ) (mu2 : ℝ) (x : KGSpatialSpace) : ℝ :=
  mu2 * L x ^ 2 * U x - ∑ i : Fin 3,
    spatialPartial (fun y => L y * spatialPartial U y i) x i

theorem spatial_hamiltonian_pointwise_quadratic (L U pi d : KGSpatialSpace → ℝ)
    (hU : ContDiff ℝ (⊤ : ℕ∞) U) (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (mu2 t : ℝ) (x : KGSpatialSpace) :
    spatialHamiltonianDensity L (fun y => U y + t * d y) pi mu2 x -
      spatialHamiltonianDensity L U pi mu2 x =
        t * spatialHamiltonianFirst L U d mu2 x + t ^ 2 * spatialHamiltonianSecond L d mu2 x := by
  simp only [spatialHamiltonianDensity, scalarCanonicalHamiltonian,
    spatial_partial_add_multiple U d hU hd t x, spatialHamiltonianFirst,
    spatialHamiltonianSecond, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  ring

theorem spatial_hamiltonian_first_integrable (L U d : KGSpatialSpace → ℝ)
    (hL : ContDiff ℝ (⊤ : ℕ∞) L) (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hd : ContDiff ℝ (⊤ : ℕ∞) d) (compact : HasCompactSupport d) (mu2 : ℝ) :
    Integrable (spatialHamiltonianFirst L U d mu2) := by
  have potential : Integrable (fun x => mu2 * L x ^ 2 * U x * d x) :=
    (((contDiff_const.mul (hL.pow 2)).mul hU).mul hd).continuous.integrable_of_hasCompactSupport compact.mul_left
  have gradient (i : Fin 3) :
      Integrable (fun x => L x * spatialPartial U x i * spatialPartial d x i) :=
    ((hL.mul (spatial_partial_smooth U hU i)).mul (spatial_partial_smooth d hd i)).continuous.integrable_of_hasCompactSupport
      (spatial_partial_compact d compact i).mul_left
  exact potential.add (integrable_finset_sum _ (fun i _ => gradient i))

theorem spatial_hamiltonian_second_integrable (L d : KGSpatialSpace → ℝ)
    (hL : ContDiff ℝ (⊤ : ℕ∞) L) (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (compact : HasCompactSupport d) (mu2 : ℝ) :
    Integrable (spatialHamiltonianSecond L d mu2) := by
  have potential : Integrable (fun x => mu2 * L x ^ 2 * d x * d x) :=
    (((contDiff_const.mul (hL.pow 2)).mul hd).mul hd).continuous.integrable_of_hasCompactSupport compact.mul_left
  have gradient (i : Fin 3) :
      Integrable (fun x => L x * spatialPartial d x i * spatialPartial d x i) :=
    ((hL.mul (spatial_partial_smooth d hd i)).mul (spatial_partial_smooth d hd i)).continuous.integrable_of_hasCompactSupport
      (spatial_partial_compact d compact i).mul_left
  exact (potential.add (integrable_finset_sum _ (fun i _ => gradient i))).const_mul (1 / 2 : ℝ)

theorem spatial_hamiltonian_relative_integrable (L U pi d : KGSpatialSpace → ℝ)
    (hL : ContDiff ℝ (⊤ : ℕ∞) L) (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hd : ContDiff ℝ (⊤ : ℕ∞) d) (compact : HasCompactSupport d) (mu2 t : ℝ) :
    Integrable (fun x => spatialHamiltonianDensity L (fun y => U y + t * d y) pi mu2 x -
      spatialHamiltonianDensity L U pi mu2 x) := by
  simp_rw [spatial_hamiltonian_pointwise_quadratic L U pi d hU hd mu2 t]
  exact ((spatial_hamiltonian_first_integrable L U d hL hU hd compact mu2).const_mul t).add
    ((spatial_hamiltonian_second_integrable L d hL hd compact mu2).const_mul (t ^ 2))

theorem spatial_hamiltonian_relative_derivative (L U pi d : KGSpatialSpace → ℝ)
    (hL : ContDiff ℝ (⊤ : ℕ∞) L) (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hd : ContDiff ℝ (⊤ : ℕ∞) d) (compact : HasCompactSupport d) (mu2 : ℝ) :
    HasDerivAt (spatialHamiltonianRelative L U pi d mu2)
      (∫ x : KGSpatialSpace, spatialHamiltonianFirst L U d mu2 x) 0 := by
  have first := spatial_hamiltonian_first_integrable L U d hL hU hd compact mu2
  have second := spatial_hamiltonian_second_integrable L d hL hd compact mu2
  have equality : spatialHamiltonianRelative L U pi d mu2 = fun t =>
      t * (∫ x : KGSpatialSpace, spatialHamiltonianFirst L U d mu2 x) +
        t ^ 2 * (∫ x : KGSpatialSpace, spatialHamiltonianSecond L d mu2 x) := by
    funext t
    unfold spatialHamiltonianRelative
    simp_rw [spatial_hamiltonian_pointwise_quadratic L U pi d hU hd mu2 t]
    rw [integral_add (first.const_mul t) (second.const_mul (t ^ 2)), integral_const_mul, integral_const_mul]
  rw [equality]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const
    (∫ x : KGSpatialSpace, spatialHamiltonianFirst L U d mu2 x)).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const
        (∫ x : KGSpatialSpace, spatialHamiltonianSecond L d mu2 x))

theorem spatial_hamiltonian_actual_euler_pairing (L U d : KGSpatialSpace → ℝ)
    (hL : ContDiff ℝ (⊤ : ℕ∞) L) (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hd : ContDiff ℝ (⊤ : ℕ∞) d) (compact : HasCompactSupport d) (mu2 : ℝ) :
    (∫ x : KGSpatialSpace, spatialHamiltonianFirst L U d mu2 x) =
      ∫ x : KGSpatialSpace, spatialHamiltonianEuler L U mu2 x * d x := by
  have fluxRegular (i : Fin 3) := hL.mul (spatial_partial_smooth U hU i)
  have igradient (i : Fin 3) :
      Integrable (fun x => L x * spatialPartial U x i * spatialPartial d x i) :=
    ((fluxRegular i).mul (spatial_partial_smooth d hd i)).continuous.integrable_of_hasCompactSupport
      (spatial_partial_compact d compact i).mul_left
  have ipotential : Integrable (fun x => mu2 * L x ^ 2 * U x * d x) :=
    (((contDiff_const.mul (hL.pow 2)).mul hU).mul hd).continuous.integrable_of_hasCompactSupport compact.mul_left
  have iflux (i : Fin 3) :
      Integrable (fun x => spatialPartial (fun y => L y * spatialPartial U y i) x i * d x) :=
    ((spatial_partial_smooth _ (fluxRegular i) i).mul hd).continuous.integrable_of_hasCompactSupport compact.mul_left
  unfold spatialHamiltonianFirst spatialHamiltonianEuler
  simp only [sub_mul, Finset.sum_mul]
  rw [integral_add ipotential (integrable_finset_sum _ (fun i _ => igradient i)),
    integral_sub ipotential (integrable_finset_sum _ (fun i _ => iflux i)),
    integral_finset_sum _ (fun i _ => igradient i), integral_finset_sum _ (fun i _ => iflux i)]
  simp_rw [spatial_compact_integration_by_parts _ d (fluxRegular _) hd compact _]
  rw [Finset.sum_neg_distrib]
  ring

theorem spatial_hamiltonian_euler_derivative (L U pi d : KGSpatialSpace → ℝ)
    (hL : ContDiff ℝ (⊤ : ℕ∞) L) (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hd : ContDiff ℝ (⊤ : ℕ∞) d) (compact : HasCompactSupport d) (mu2 : ℝ) :
    HasDerivAt (spatialHamiltonianRelative L U pi d mu2)
      (∫ x : KGSpatialSpace, spatialHamiltonianEuler L U mu2 x * d x) 0 := by
  rw [← spatial_hamiltonian_actual_euler_pairing L U d hL hU hd compact mu2]
  exact spatial_hamiltonian_relative_derivative L U pi d hL hU hd compact mu2

end AASCKleinGordon.SameActionSource
