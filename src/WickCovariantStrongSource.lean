import WickCovariantKernelTest
import WickStrongCoreControl

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000
open Filter Topology
open scoped SchwartzMap
namespace AASCKleinGordon
attribute [local irreducible] originalWickRaisedStressDistribution wickCovariantOriginalCore

instance wickCovariantAntidualTopologicalAddGroup :
    IsTopologicalAddGroup (𝓢(Momentum,ℂ) →L⋆[ℂ] ℂ) :=
  ContinuousLinearMap.topologicalAddGroup (E:=𝓢(Momentum,ℂ)) (F:=ℂ) (σ:=starRingEnd ℂ)

instance wickCovariantAntidualContinuousAdd : ContinuousAdd (𝓢(Momentum,ℂ) →L⋆[ℂ] ℂ) :=
  wickCovariantAntidualTopologicalAddGroup.toContinuousAdd

theorem wick_covariant_core_control_bounded (a : Parameters)
    (P : Seminorm ℂ FiniteParticleCore) (hP : Continuous P)
    (S : Set 𝓢(Momentum,ℂ)) (hS : Bornology.IsVonNBounded ℂ S) :
    ∃ M > 0,∀ f∈S,P (wickCovariantOriginalCore a f)<M := by
  obtain ⟨M,hM,hb⟩ := wick_continuous_core_seminorm_bounded P hP _
    (hS.image (wickCovariantOriginalCore a))
  exact ⟨M,hM,fun f hf => hb _ ⟨f,hf,rfl⟩⟩

/-- Strong antidual topology means uniform convergence on von Neumann
bounded sets of the actual Schwartz topology. -/
theorem wick_covariant_strong_continuous_of_bound
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (a : Parameters) (L : X →+ (𝓢(Momentum,ℂ) →L⋆[ℂ] ℂ))
    (b : X → ℝ) (hb : Continuous b) (hb0 : b 0=0) (hbpos : ∀ x,0≤b x)
    (P : Seminorm ℂ FiniteParticleCore) (hP : Continuous P)
    (hbound : ∀ x f,‖L x f‖≤b x*P (wickCovariantOriginalCore a f)) : Continuous L := by
  apply continuous_of_continuousAt_zero L
  change Tendsto L (𝓝 0) (𝓝 (L 0))
  rw [map_zero]
  apply (ContinuousLinearMap.hasBasis_nhds_zero_of_basis
    (E:=𝓢(Momentum,ℂ)) (F:=ℂ) (σ:=starRingEnd ℂ)
    (Metric.nhds_basis_ball (x:=(0:ℂ)))).tendsto_right_iff.mpr
  rintro ⟨S,ε⟩ ⟨hS,hε⟩
  obtain ⟨M,hM,hPM⟩ := wick_covariant_core_control_bounded a P hP S hS
  have hs : ∀ᶠ x in 𝓝 (0:X),b x<ε/M :=
    hb.tendsto 0 (Iio_mem_nhds (by simpa only [hb0] using div_pos hε hM))
  filter_upwards [hs] with x hx
  intro f hf
  change dist (L x f) 0<ε
  rw [dist_zero_right]
  exact ((hbound x f).trans (mul_le_mul_of_nonneg_left (hPM f hf).le (hbpos x))).trans_lt
    ((lt_div_iff₀ hM).mp hx)

theorem wick_covariant_source_operator_strong_continuous (a : Parameters) (s : ℝ)
    (i j : Fin 4) (h : 𝓢(Spacetime,ℂ)) :
    Continuous (wickCovariantSourceOperatorLM a s i j h) := by
  apply wick_covariant_strong_continuous_of_bound a
    (wickCovariantSourceOperatorLM a s i j h).toAddMonoidHom
    (fun g => wickOriginalRightCoreSeminorm a (wickCovariantOriginalCore a g)*
      ‖h.toLp 1 MeasureTheory.volume‖)
    (((wick_original_right_core_seminorm_continuous a).comp
      (wickCovariantOriginalCore a).continuous).mul continuous_const)
    (by simp) (fun g => mul_nonneg (apply_nonneg _ _) (norm_nonneg _))
    (wickOriginalLeftCoreSeminorm a s) (wick_original_left_core_seminorm_continuous a s)
  intro g f
  apply (wick_original_raised_stress_continuous_bound a s i j
    (wickCovariantOriginalCore a f) (wickCovariantOriginalCore a g) h).trans_eq
  ring

def wickCovariantSourceOperator (a : Parameters) (s : ℝ) (i j : Fin 4) (h : 𝓢(Spacetime,ℂ)) :
    𝓢(Momentum,ℂ) →L[ℂ] (𝓢(Momentum,ℂ) →L⋆[ℂ] ℂ) :=
  { toLinearMap := wickCovariantSourceOperatorLM a s i j h
    cont := wick_covariant_source_operator_strong_continuous a s i j h }

instance wickCovariantDoubleStrongAddCommGroup :
    AddCommGroup (𝓢(Momentum,ℂ) →L[ℂ] (𝓢(Momentum,ℂ) →L⋆[ℂ] ℂ)) :=
  ContinuousLinearMap.addCommGroup (R:=ℂ) (R₂:=ℂ) (M:=𝓢(Momentum,ℂ))
    (M₂:=𝓢(Momentum,ℂ) →L⋆[ℂ] ℂ) (σ₁₂:=RingHom.id ℂ)

instance wickCovariantDoubleStrongTopology :
    TopologicalSpace (𝓢(Momentum,ℂ) →L[ℂ] (𝓢(Momentum,ℂ) →L⋆[ℂ] ℂ)) :=
  ContinuousLinearMap.topologicalSpace (E:=𝓢(Momentum,ℂ))
    (F:=𝓢(Momentum,ℂ) →L⋆[ℂ] ℂ) (σ:=RingHom.id ℂ)

instance wickCovariantDoubleStrongTopologicalAddGroup :
    IsTopologicalAddGroup (𝓢(Momentum,ℂ) →L[ℂ] (𝓢(Momentum,ℂ) →L⋆[ℂ] ℂ)) :=
  ContinuousLinearMap.topologicalAddGroup (E:=𝓢(Momentum,ℂ))
    (F:=𝓢(Momentum,ℂ) →L⋆[ℂ] ℂ) (σ:=RingHom.id ℂ)

instance wickCovariantDoubleStrongContinuousAdd :
    ContinuousAdd (𝓢(Momentum,ℂ) →L[ℂ] (𝓢(Momentum,ℂ) →L⋆[ℂ] ℂ)) :=
  wickCovariantDoubleStrongTopologicalAddGroup.toContinuousAdd

def wickCovariantStrongSourceLM (a : Parameters) (s : ℝ) (i j : Fin 4) :
    𝓢(Spacetime,ℂ) →ₗ[ℂ] (𝓢(Momentum,ℂ) →L[ℂ] (𝓢(Momentum,ℂ) →L⋆[ℂ] ℂ)) where
  toFun h := wickCovariantSourceOperator a s i j h
  map_add' h k := by
    ext g f
    change wickCovariantSourceForm a s i j f g (h+k)=_
    exact map_add _ h k
  map_smul' c h := by
    ext g f
    change wickCovariantSourceForm a s i j f g (c • h)=_
    exact map_smul _ c h

theorem wick_covariant_source_double_strong_continuous (a : Parameters) (s : ℝ) (i j : Fin 4) :
    Continuous (wickCovariantStrongSourceLM a s i j) := by
  let L := (wickCovariantStrongSourceLM a s i j).toAddMonoidHom
  apply continuous_of_continuousAt_zero L
  change Tendsto L (𝓝 0) (𝓝 (L 0))
  rw [map_zero]
  let hdual := ContinuousLinearMap.hasBasis_nhds_zero_of_basis
    (E:=𝓢(Momentum,ℂ)) (F:=ℂ) (σ:=starRingEnd ℂ) (Metric.nhds_basis_ball (x:=(0:ℂ)))
  apply (ContinuousLinearMap.hasBasis_nhds_zero_of_basis
    (E:=𝓢(Momentum,ℂ)) (F:=𝓢(Momentum,ℂ) →L⋆[ℂ] ℂ) (σ:=RingHom.id ℂ) hdual).tendsto_right_iff.mpr
  rintro ⟨S,T,ε⟩ ⟨hS,hT,hε⟩
  obtain ⟨M,hM,hQM⟩ := wick_covariant_core_control_bounded a
    (wickOriginalRightCoreSeminorm a) (wick_original_right_core_seminorm_continuous a) S hS
  obtain ⟨N,hN,hPN⟩ := wick_covariant_core_control_bounded a
    (wickOriginalLeftCoreSeminorm a s) (wick_original_left_core_seminorm_continuous a s) T hT
  have hc := (SchwartzMap.toLpCLM ℝ ℂ 1 (MeasureTheory.volume : MeasureTheory.Measure Spacetime)).continuous.norm
  have hs : ∀ᶠ h in 𝓝 (0:𝓢(Spacetime,ℂ)),‖h.toLp 1 MeasureTheory.volume‖<ε/(M*N) :=
    hc.tendsto 0 (Iio_mem_nhds (by
      change ‖(SchwartzMap.toLpCLM ℝ ℂ 1 (MeasureTheory.volume : MeasureTheory.Measure Spacetime)) 0‖<ε/(M*N)
      simpa only [map_zero,norm_zero] using div_pos hε (mul_pos hM hN)))
  filter_upwards [hs] with h hh
  intro g hg f hf
  change dist (L h g f) 0<ε
  rw [dist_zero_right]
  calc
    _ ≤ wickOriginalLeftCoreSeminorm a s (wickCovariantOriginalCore a f)*
        wickOriginalRightCoreSeminorm a (wickCovariantOriginalCore a g)*‖h.toLp 1 MeasureTheory.volume‖ :=
      wick_original_raised_stress_continuous_bound a s i j _ _ h
    _ ≤ N*M*‖h.toLp 1 MeasureTheory.volume‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul (hPN f hf).le (hQM g hg).le
        (apply_nonneg _ _) hN.le) (norm_nonneg _)
    _ < ε := by nlinarith [(lt_div_iff₀ (mul_pos hM hN)).mp hh]

def wickCovariantStrongSource (a : Parameters) (s : ℝ) (i j : Fin 4) :
    𝓢(Spacetime,ℂ) →L[ℂ] (𝓢(Momentum,ℂ) →L[ℂ] (𝓢(Momentum,ℂ) →L⋆[ℂ] ℂ)) :=
  { toLinearMap := wickCovariantStrongSourceLM a s i j
    cont := wick_covariant_source_double_strong_continuous a s i j }

theorem wick_covariant_strong_source_same_tensor (a : Parameters) (s : ℝ) (i j : Fin 4)
    (f g : 𝓢(Momentum,ℂ)) (h : 𝓢(Spacetime,ℂ)) :
    wickCovariantStrongSource a s i j h g f=
      originalWickRaisedStressDistribution a s
        (wickCovariantOriginalCore a f) (wickCovariantOriginalCore a g) i j h := rfl

theorem wick_covariant_strong_kernel_square (a : Parameters) (s : ℝ) (i j : Fin 4)
    (f g : 𝓢(Momentum,ℂ)) (h : 𝓢(Spacetime,ℂ)) :
    wickCovariantKernelMomentumCLM a s i j h (wickCovariantPairTest f g)=
      wickCovariantStrongSource a s i j h g f :=
  wick_covariant_kernel_source_square a s i j f g h

end AASCKleinGordon
