import WickOriginalCoreControls
import Mathlib.Topology.Algebra.Module.StrongTopology

noncomputable section
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000
open scoped NNReal Topology
open TopologicalSpace Filter
namespace AASCKleinGordon

instance wickStrongAntidualTopologicalAddGroup :
    IsTopologicalAddGroup (FiniteParticleCore →L⋆[ℂ] ℂ) :=
  ContinuousLinearMap.topologicalAddGroup (E:=FiniteParticleCore) (F:=ℂ) (σ:=starRingEnd ℂ)

instance wickStrongAntidualContinuousAdd :
    ContinuousAdd (FiniteParticleCore →L⋆[ℂ] ℂ) :=
  wickStrongAntidualTopologicalAddGroup.toContinuousAdd

instance wickDoubleStrongAddCommGroup :
    AddCommGroup (FiniteParticleCore →L[ℂ] (FiniteParticleCore →L⋆[ℂ] ℂ)) :=
  ContinuousLinearMap.addCommGroup (R:=ℂ) (R₂:=ℂ) (M:=FiniteParticleCore)
    (M₂:=FiniteParticleCore →L⋆[ℂ] ℂ) (σ₁₂:=RingHom.id ℂ)

instance wickDoubleStrongTopology :
    TopologicalSpace (FiniteParticleCore →L[ℂ] (FiniteParticleCore →L⋆[ℂ] ℂ)) :=
  ContinuousLinearMap.topologicalSpace (E:=FiniteParticleCore)
    (F:=FiniteParticleCore →L⋆[ℂ] ℂ) (σ:=RingHom.id ℂ)

instance wickDoubleStrongTopologicalAddGroup :
    IsTopologicalAddGroup (FiniteParticleCore →L[ℂ] (FiniteParticleCore →L⋆[ℂ] ℂ)) :=
  ContinuousLinearMap.topologicalAddGroup (E:=FiniteParticleCore)
    (F:=FiniteParticleCore →L⋆[ℂ] ℂ) (σ:=RingHom.id ℂ)

instance wickDoubleStrongContinuousAdd :
    ContinuousAdd (FiniteParticleCore →L[ℂ] (FiniteParticleCore →L⋆[ℂ] ℂ)) :=
  wickDoubleStrongTopologicalAddGroup.toContinuousAdd

lemma wick_continuous_core_seminorm_bounded (Q : Seminorm ℂ FiniteParticleCore)
    (hQ : Continuous Q) (S : Set FiniteParticleCore) (hS : Bornology.IsVonNBounded ℂ S) :
    ∃ M > 0, ∀ u ∈ S,Q u < M := by
  let i : CoreSeminormIndex := ⟨Q,fun n => hQ.comp (finiteParticleCore_lof_continuous n)⟩
  exact finiteParticleCore_withSeminorms.isVonNBounded_iff_seminorm_bounded.mp hS i

/-- Continuity into the actual topology of uniform convergence on bounded
core sets, derived from a proved uniform seminorm estimate. -/
lemma wick_core_strong_continuous_of_bound
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (L : X →+ (FiniteParticleCore →L⋆[ℂ] ℂ))
    (b : X → ℝ) (hb : Continuous b) (hb0 : b 0=0) (hbpos : ∀ x,0≤b x)
    (Q : Seminorm ℂ FiniteParticleCore) (hQ : Continuous Q)
    (hbound : ∀ x u,‖L x u‖≤b x*Q u) : Continuous L := by
  apply continuous_of_continuousAt_zero L
  change Tendsto L (𝓝 0) (𝓝 (L 0))
  rw [map_zero]
  apply (ContinuousLinearMap.hasBasis_nhds_zero_of_basis
    (E:=FiniteParticleCore) (F:=ℂ) (σ:=starRingEnd ℂ) (Metric.nhds_basis_ball (x:=(0:ℂ)))).tendsto_right_iff.mpr
  rintro ⟨S,ε⟩ ⟨hS,hε⟩
  obtain ⟨M,hM,hQM⟩ := wick_continuous_core_seminorm_bounded Q hQ S hS
  have hsmall : ∀ᶠ x in 𝓝 (0:X),b x<ε/M :=
    hb.tendsto 0 (Iio_mem_nhds (by simpa only [hb0] using div_pos hε hM))
  filter_upwards [hsmall] with x hx
  intro u hu
  change dist (L x u) 0<ε
  rw [dist_zero_right]
  calc
    ‖L x u‖≤b x*Q u := hbound x u
    _ ≤ b x*M := mul_le_mul_of_nonneg_left (hQM u hu).le (hbpos x)
    _ < ε := (lt_div_iff₀ hM).mp hx

/-- The same estimate gives continuity into continuous core operators valued
in the strong antidual. The target uses bounded convergence at both levels. -/
lemma wick_core_double_strong_continuous_of_bound
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (L : X →+ (FiniteParticleCore →L[ℂ] (FiniteParticleCore →L⋆[ℂ] ℂ)))
    (b : X → ℝ) (hb : Continuous b) (hb0 : b 0=0) (hbpos : ∀ x,0≤b x)
    (P Q : Seminorm ℂ FiniteParticleCore) (hP : Continuous P) (hQ : Continuous Q)
    (hbound : ∀ x v u,‖L x v u‖≤b x*Q v*P u) : Continuous L := by
  apply continuous_of_continuousAt_zero L
  change Tendsto L (𝓝 0) (𝓝 (L 0))
  rw [map_zero]
  let hdual := ContinuousLinearMap.hasBasis_nhds_zero_of_basis
    (E:=FiniteParticleCore) (F:=ℂ) (σ:=starRingEnd ℂ) (Metric.nhds_basis_ball (x:=(0:ℂ)))
  apply (ContinuousLinearMap.hasBasis_nhds_zero_of_basis
    (E:=FiniteParticleCore) (F:=FiniteParticleCore →L⋆[ℂ] ℂ) (σ:=RingHom.id ℂ) hdual).tendsto_right_iff.mpr
  rintro ⟨S,T,ε⟩ ⟨hS,hT,hε⟩
  obtain ⟨M,hM,hQM⟩ := wick_continuous_core_seminorm_bounded Q hQ S hS
  obtain ⟨N,hN,hPN⟩ := wick_continuous_core_seminorm_bounded P hP T hT
  have hsmall : ∀ᶠ x in 𝓝 (0:X),b x<ε/(M*N) :=
    hb.tendsto 0 (Iio_mem_nhds (by simpa only [hb0] using div_pos hε (mul_pos hM hN)))
  filter_upwards [hsmall] with x hx
  intro v hv u hu
  change dist (L x v u) 0<ε
  rw [dist_zero_right]
  calc
    ‖L x v u‖≤b x*Q v*P u := hbound x v u
    _ ≤ b x*M*N := mul_le_mul
      (mul_le_mul_of_nonneg_left (hQM v hv).le (hbpos x)) (hPN u hu).le
      (apply_nonneg _ _) (mul_nonneg (hbpos x) hM.le)
    _ < ε := by simpa only [mul_assoc] using (lt_div_iff₀ (mul_pos hM hN)).mp hx

end AASCKleinGordon
