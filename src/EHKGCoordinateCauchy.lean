import EHKGFullFlatSmooth
import EHKGProtectedConformalChart

/-! Exact coordinate/derivative connection from the full smooth Fourier family
to the inherited scalar coordinate operator. No assumed solution agreement. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped SchwartzMap FourierTransform Topology BigOperators
namespace AASCKleinGordon.CurvedKG

def coordinateSpatialSplit : CoordinatePoint ≃L[ℝ] (ℝ × KGSpatialSpace) :=
  wickSpacetimeCoordinates.symm.trans spacetimeSpatialJoin.symm

theorem coordinate_split_time (p : CoordinatePoint) : (coordinateSpatialSplit p).1 = p 0 := rfl

theorem coordinate_split_space (p : CoordinatePoint) :
    (coordinateSpatialSplit p).2 = momentumEuclidean (Fin.tail p) := rfl

theorem coordinate_split_time_curve (p : CoordinatePoint) (s : ℝ) :
    coordinateSpatialSplit (p + s • (Pi.single (0 : Fin 4) (1 : ℝ) : CoordinatePoint)) =
      (p 0 + s, (coordinateSpatialSplit p).2) := by
  apply Prod.ext
  · simp [coordinate_split_time, Pi.single_apply]
  · rw [coordinate_split_space, coordinate_split_space]
    congr 1
    funext i
    simp [Fin.tail, Pi.single_apply]

theorem coordinate_split_space_curve (p : CoordinatePoint) (s : ℝ) (i : Fin 3) :
    coordinateSpatialSplit (p + s • (Pi.single i.succ (1 : ℝ) : CoordinatePoint)) =
      (p 0, (coordinateSpatialSplit p).2 + s • kgSpatialDirection i) := by
  apply Prod.ext
  · simp [coordinate_split_time, Pi.single_apply]
  · rw [coordinate_split_space, coordinate_split_space]
    ext j
    change p j.succ + s * (Pi.single i.succ (1 : ℝ) : CoordinatePoint) j.succ =
      p j.succ + s * (kgSpatialDirection i) j
    simp [Pi.single_apply, kgSpatialDirection, EuclideanSpace.single_apply]

theorem scalar_partial_of_curve (F : CoordinatePoint → ℝ) (p : CoordinatePoint) (c : Fin 4)
    (regular : DifferentiableAt ℝ F p) (r : ℝ)
    (curve : HasDerivAt (fun s : ℝ => F (p + s • (Pi.single c (1 : ℝ) : CoordinatePoint))) r 0) : scalarPartial F p c = r := by
  have line : HasDerivAt (fun s : ℝ => p + s • (Pi.single c (1 : ℝ) : CoordinatePoint)) (Pi.single c 1) 0 := by
    have raw := (hasDerivAt_const (0 : ℝ) p).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single c (1 : ℝ) : CoordinatePoint))
    simpa only [Pi.add_apply, zero_add, one_smul] using raw
  have actual : HasDerivAt (fun s : ℝ => F (p + s • (Pi.single c (1 : ℝ) : CoordinatePoint))) (scalarPartial F p c) 0 := by
    have atLine : HasFDerivAt F (fderiv ℝ F p) (p + (0 : ℝ) • (Pi.single c (1 : ℝ) : CoordinatePoint)) := by
      simpa only [zero_smul, add_zero] using regular.hasFDerivAt
    simpa only [scalarPartial] using atLine.comp_hasDerivAt 0 line
  exact actual.unique curve

def flatCoordinateField (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ)) (P : ℂ →L[ℝ] ℝ)
    (p : CoordinatePoint) : ℝ :=
  P (fullFlatPosition a f h (coordinateSpatialSplit p).1 (coordinateSpatialSplit p).2)

theorem flat_coordinate_smooth (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ)) (P : ℂ →L[ℝ] ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (flatCoordinateField a f h P) :=
  P.contDiff.comp ((full_flat_joint_smooth a f h).comp coordinateSpatialSplit.contDiff)

theorem full_flat_velocity_as_position (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ)) (t : ℝ) :
    fullFlatVelocity a f h t = fullFlatPosition a h (-kgSpatialOperator a f) t := by
  simp only [fullFlatVelocity, fullFlatPosition, map_neg]
  abel

theorem flat_coordinate_time_partial (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ))
    (P : ℂ →L[ℝ] ℝ) (p : CoordinatePoint) :
    scalarPartial (flatCoordinateField a f h P) p 0 =
      flatCoordinateField a h (-kgSpatialOperator a f) P p := by
  apply scalar_partial_of_curve _ p 0 ((flat_coordinate_smooth a f h P).differentiable (by simp) p)
  simp only [flatCoordinateField, coordinate_split_time_curve, Prod.fst, Prod.snd]
  have first := P.hasFDerivAt.comp_hasDerivAt (p 0)
    (full_flat_position_hasDerivAt a f h (p 0) (coordinateSpatialSplit p).2)
  have atShift : HasDerivAt
      (fun t => P (fullFlatPosition a f h t (coordinateSpatialSplit p).2))
      (P (fullFlatVelocity a f h (p 0) (coordinateSpatialSplit p).2)) (p 0 + (0 : ℝ)) := by
    simpa only [add_zero] using first
  have shift : HasDerivAt (fun s : ℝ => p 0 + s) 1 0 := by
    simpa only [id_eq] using (hasDerivAt_id (0 : ℝ)).const_add (p 0)
  simpa [coordinate_split_time, full_flat_velocity_as_position] using
    atShift.comp (0 : ℝ) shift

theorem flat_coordinate_space_partial (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ))
    (P : ℂ →L[ℝ] ℝ) (p : CoordinatePoint) (i : Fin 3) :
    scalarPartial (flatCoordinateField a f h P) p i.succ =
      flatCoordinateField a (kgSpatialPartialCLM i f) (kgSpatialPartialCLM i h) P p := by
  apply scalar_partial_of_curve _ p i.succ ((flat_coordinate_smooth a f h P).differentiable (by simp) p)
  simp only [flatCoordinateField, coordinate_split_space_curve, Prod.fst, Prod.snd]
  have line : HasDerivAt (fun s : ℝ => (coordinateSpatialSplit p).2 + s • kgSpatialDirection i)
      (kgSpatialDirection i) 0 := by
    have raw := (hasDerivAt_const (0 : ℝ) (coordinateSpatialSplit p).2).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (kgSpatialDirection i))
    simpa only [Pi.add_apply, zero_add, one_smul] using raw
  have atLine : HasFDerivAt (fullFlatPosition a f h (p 0))
      (fderiv ℝ (fullFlatPosition a f h (p 0)) (coordinateSpatialSplit p).2)
      ((coordinateSpatialSplit p).2 + (0 : ℝ) • kgSpatialDirection i) := by
    simpa only [zero_smul, add_zero] using
      (fullFlatPosition a f h (p 0)).hasFDerivAt (coordinateSpatialSplit p).2
  have first := P.hasFDerivAt.comp_hasDerivAt 0
    (atLine.comp_hasDerivAt 0 line)
  simpa only [kgSpatialPartial_apply, ← full_flat_position_spatial_partial,
    coordinate_split_time] using first

theorem flat_coordinate_time_second (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ))
    (P : ℂ →L[ℝ] ℝ) (p : CoordinatePoint) :
    scalarSecondPartial (flatCoordinateField a f h P) p 0 0 =
      P (fullFlatAcceleration a f h (p 0) (coordinateSpatialSplit p).2) := by
  unfold scalarSecondPartial
  simp_rw [flat_coordinate_time_partial]
  change P (fullFlatPosition a (-kgSpatialOperator a f) (-kgSpatialOperator a h)
    (coordinateSpatialSplit p).1 (coordinateSpatialSplit p).2) = _
  simp [fullFlatPosition, fullFlatAcceleration, map_neg, coordinate_split_time, sub_eq_add_neg, add_comm]

theorem flat_coordinate_space_second (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ))
    (P : ℂ →L[ℝ] ℝ) (p : CoordinatePoint) (i : Fin 3) :
    scalarSecondPartial (flatCoordinateField a f h P) p i.succ i.succ =
      P (kgSpatialPartialCLM i (kgSpatialPartialCLM i (fullFlatPosition a f h (p 0)))
        (coordinateSpatialSplit p).2) := by
  unfold scalarSecondPartial
  simp_rw [flat_coordinate_space_partial]
  rw [full_flat_position_spatial_partial, full_flat_position_spatial_partial]
  rfl

theorem flat_coordinate_residual_zero (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ))
    (P : ℂ →L[ℝ] ℝ) (p : CoordinatePoint) :
    flatScalarResidual ((massWaveNumber a) ^ 2) (flatCoordinateField a f h P) p = 0 := by
  have equation := congrArg (fun F : 𝓢(KGSpatialSpace, ℂ) => P (F (coordinateSpatialSplit p).2))
    (full_flat_acceleration_equation a (p 0) f h)
  simp only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, P.map_sub] at equation
  rw [← Complex.ofReal_pow, realProjection_complex_smul] at equation
  have laplacian : P (kgSpatialLaplacian (fullFlatPosition a f h (p 0)) (coordinateSpatialSplit p).2) =
      scalarSecondPartial (flatCoordinateField a f h P) p 1 1 +
      scalarSecondPartial (flatCoordinateField a f h P) p 2 2 +
      scalarSecondPartial (flatCoordinateField a f h P) p 3 3 := by
    have first := flat_coordinate_space_second a f h P p 0
    have second := flat_coordinate_space_second a f h P p 1
    have third := flat_coordinate_space_second a f h P p 2
    simp only [Fin.reduceSucc] at first second third
    rw [first, second, third]
    simp [kgSpatialLaplacian, Fin.sum_univ_three, SchwartzMap.add_apply, P.map_add]
  dsimp [flatScalarResidual]
  rw [flat_coordinate_time_second, equation, laplacian]
  change _ - _ - _ - _ + _ * P (fullFlatPosition a f h (p 0) (coordinateSpatialSplit p).2) = 0
  ring

end AASCKleinGordon.CurvedKG
