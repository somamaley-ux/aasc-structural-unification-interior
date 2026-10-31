/-!
# Capstone: named whole-stack realization obligations

The module developments prove their algebraic consequences.  The remaining
paper-specific realization steps are named here individually so that the
capstone cannot hide them behind an undifferentiated certificate field.
-/

namespace AASCStack

structure CapstoneObligations where
  kernelClosure : Prop
  gravityGeometricBridge : Prop
  moduleAFullTensorDensity : Prop
  moduleBStoneRealization : Prop
  moduleCUpstreamSeed : Prop
  moduleDPaperInstantiation : Prop

structure CapstoneCertificate (O : CapstoneObligations) where
  kernel : O.kernelClosure
  gravity : O.gravityGeometricBridge
  moduleA : O.moduleAFullTensorDensity
  moduleB : O.moduleBStoneRealization
  moduleC : O.moduleCUpstreamSeed
  moduleD : O.moduleDPaperInstantiation

theorem CapstoneCertificate.all_realization_obligations
    {O : CapstoneObligations} (C : CapstoneCertificate O) :
    O.kernelClosure ∧ O.gravityGeometricBridge ∧
      O.moduleAFullTensorDensity ∧ O.moduleBStoneRealization ∧
      O.moduleCUpstreamSeed ∧ O.moduleDPaperInstantiation := by
  exact ⟨C.kernel, C.gravity, C.moduleA, C.moduleB, C.moduleC, C.moduleD⟩

theorem CapstoneCertificate.requires_gravity_bridge
    {O : CapstoneObligations} (C : CapstoneCertificate O) :
    O.gravityGeometricBridge :=
  C.gravity

theorem CapstoneCertificate.requires_moduleB_Stone
    {O : CapstoneObligations} (C : CapstoneCertificate O) :
    O.moduleBStoneRealization :=
  C.moduleB

end AASCStack
