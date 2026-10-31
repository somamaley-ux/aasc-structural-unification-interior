import KGWickLocalStressConservation

noncomputable section
set_option maxHeartbeats 8000000
open scoped BigOperators
namespace AASCKleinGordon

abbrev WickStressInput := (Fin 4 → Fin 4 → ℂ) × ℂ

def wickRaisedStressReadout (a : Parameters) (i j : Fin 4) : WickStressInput →ₗ[ℂ] ℂ where
  toFun U := (wickFlatSign i : ℂ)*(wickFlatSign j : ℂ)*
    ((1/2 : ℂ)*(U.1 i j+U.1 j i)-((wickFlatMetricComponent i j : ℂ)/2)*
      (-U.1 0 0+U.1 1 1+U.1 2 2+U.1 3 3+(massWaveNumber a : ℂ)^2*U.2))
  map_add' := by intro U V; simp; ring
  map_smul' := by intro c U; simp [smul_eq_mul]; ring

def wickCoreStressInput (a : Parameters) (n : ℕ) (u v : FiniteParticleCore)
    (k : Fin 4) (x : Spacetime) : WickStressInput :=
  (fun i j => wickCoreChannelMixedMatrix a n u v k (spacetimeCoordinateVector i) (spacetimeCoordinateVector j) x x,
    wickCoreChannelMatrix a n u v k x x)

def originalWickStressInput (a : Parameters) (s : ℝ) (u v : FiniteParticleCore) (x : Spacetime) :
    WickStressInput :=
  (fun i j => originalDerivativeWickMatrix a s u v (spacetimeCoordinateVector i) (spacetimeCoordinateVector j) x,
    originalWickSquareMatrix a s u v x)

def wickCoreRaisedStressMatrix (a : Parameters) (n : ℕ) (u v : FiniteParticleCore)
    (k : Fin 4) (i j : Fin 4) : Spacetime → ℂ :=
  wickRaisedStressLocalMatrix a (n+2) (wickCoreChannelFrequency0 a n k)
    (wickCoreChannelFrequency1 a n k) (wickCoreChannelStateKernel n u v k) i j

theorem original_wick_stress_input_expansion (a : Parameters) (s : ℝ) (u v : FiniteParticleCore) (x : Spacetime) :
    originalWickStressInput a s u v x=(s : ℂ)^2 •
      ∑ k∈(Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4)),
        wickCoreChannelCoefficient k.1 k.2 • wickCoreStressInput a k.1 u v k.2 x := by
  let S := (Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4))
  let F (k : ℕ × Fin 4) : WickStressInput := wickCoreChannelCoefficient k.1 k.2 • wickCoreStressInput a k.1 u v k.2 x
  have hf (i j : Fin 4) : (∑ k∈S,F k).1 i j=∑ k∈S,wickCoreChannelCoefficient k.1 k.2*
      wickCoreChannelMixedMatrix a k.1 u v k.2 (spacetimeCoordinateVector i) (spacetimeCoordinateVector j) x x := by
    let L : WickStressInput →ₗ[ℂ] ℂ :=
      { toFun := fun U => U.1 i j
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
    have hm := map_sum L F S
    change (∑ k∈S,F k).1 i j=∑ k∈S,(F k).1 i j at hm
    simpa [F,wickCoreStressInput,smul_eq_mul] using hm
  have hs : (∑ k∈S,F k).2=∑ k∈S,wickCoreChannelCoefficient k.1 k.2*wickCoreChannelMatrix a k.1 u v k.2 x x := by
    have hm := map_sum (LinearMap.snd ℂ (Fin 4 → Fin 4 → ℂ) ℂ) F S
    change (∑ k∈S,F k).2=∑ k∈S,(F k).2 at hm
    simpa [F,wickCoreStressInput,smul_eq_mul] using hm
  apply Prod.ext
  · funext i j
    change (s : ℂ)^2*(∑ k∈S,wickCoreChannelCoefficient k.1 k.2*
      wickCoreChannelMixedMatrix a k.1 u v k.2 (spacetimeCoordinateVector i) (spacetimeCoordinateVector j) x x)=
      (s : ℂ)^2*(∑ k∈S,F k).1 i j
    exact congrArg (fun z : ℂ => (s : ℂ)^2*z) (hf i j).symm
  · change (s : ℂ)^2*(∑ k∈S,wickCoreChannelCoefficient k.1 k.2*wickCoreChannelMatrix a k.1 u v k.2 x x)=
      (s : ℂ)^2*(∑ k∈S,F k).2
    exact congrArg (fun z : ℂ => (s : ℂ)^2*z) hs.symm

theorem original_wick_raised_stress_readout (a : Parameters) (s : ℝ) (u v : FiniteParticleCore)
    (i j : Fin 4) (x : Spacetime) :
    wickRaisedStressReadout a i j (originalWickStressInput a s u v x)=
      originalWickScalarStressRaisedMatrix a s u v i j x := by
  simp [wickRaisedStressReadout,originalWickStressInput,originalWickScalarStressRaisedMatrix,
    originalWickScalarStressCandidateMatrix,originalWickScalarLagrangianMatrix]

theorem wick_core_raised_stress_readout (a : Parameters) (n : ℕ) (u v : FiniteParticleCore)
    (k : Fin 4) (i j : Fin 4) (x : Spacetime) :
    wickRaisedStressReadout a i j (wickCoreStressInput a n u v k x)=
      wickCoreRaisedStressMatrix a n u v k i j x := by
  unfold wickCoreRaisedStressMatrix
  rw [wick_raised_stress_local_formula a (n+2) _ _
    (wickCoreChannelFrequency0_temperate a n k) (wickCoreChannelFrequency1_temperate a n k)]
  simp only [wickRaisedStressReadout,LinearMap.coe_mk,AddHom.coe_mk,wickCoreStressInput,
    wickCoreChannelMixedMatrix_diagonal,wickCoreChannelMatrix_diagonal]
  rfl

theorem original_wick_raised_stress_channel_expansion (a : Parameters) (s : ℝ) (u v : FiniteParticleCore)
    (i j : Fin 4) (x : Spacetime) :
    originalWickScalarStressRaisedMatrix a s u v i j x=(s : ℂ)^2*
      ∑ k∈(Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4)),
        wickCoreChannelCoefficient k.1 k.2*wickCoreRaisedStressMatrix a k.1 u v k.2 i j x := by
  rw [← original_wick_raised_stress_readout,original_wick_stress_input_expansion]
  simp only [map_smul,map_sum,smul_eq_mul,wick_core_raised_stress_readout]

theorem wick_core_raised_stress_smooth (a : Parameters) (n : ℕ) (u v : FiniteParticleCore)
    (k i j : Fin 4) : ContDiff ℝ (⊤ : ℕ∞) (wickCoreRaisedStressMatrix a n u v k i j) :=
  wick_raised_stress_local_smooth a (n+2) _ _
    (wickCoreChannelFrequency0_temperate a n k) (wickCoreChannelFrequency1_temperate a n k) _ i j

theorem wick_core_raised_stress_conserved (a : Parameters) (n : ℕ) (u v : FiniteParticleCore)
    (k j : Fin 4) (x : Spacetime) :
    (∑ i,fderiv ℝ (wickCoreRaisedStressMatrix a n u v k i j) x (spacetimeCoordinateVector i))=0 :=
  wick_raised_stress_local_conserved a (n+2) _ _
    (wickCoreChannelFrequency0_temperate a n k) (wickCoreChannelFrequency1_temperate a n k)
    (wick_core_frequency0_stress_shell a n k) (wick_core_frequency1_stress_shell a n k) _ j x

end AASCKleinGordon
