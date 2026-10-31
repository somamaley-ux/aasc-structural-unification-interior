import KGRawQuantumOperations

/-! Coherence is proved on all algebraic tensor vectors through equality of
the actual linear maps, not only on product representatives. -/
noncomputable section
namespace AASCKleinGordon
open scoped TensorProduct
open KGQuantum
variable (E F G H : Type)
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def kgRawTensorUnit : PureVector ℂ := ⟨1,one_ne_zero⟩

theorem kg_raw_associator (x : PureVector E) (y : PureVector F) (z : PureVector G) :
    PureVector.mapUnitary (TensorProduct.assocIsometry ℂ E F G)
      (kgRawTensor (kgRawTensor x y) z) = kgRawTensor x (kgRawTensor y z) := by
  apply Subtype.ext
  simp [kgRawTensor]

theorem kg_raw_left_unitor (x : PureVector E) :
    PureVector.mapUnitary (TensorProduct.lidIsometry ℂ E)
      (kgRawTensor kgRawTensorUnit x)=x := by
  apply Subtype.ext
  simp [kgRawTensor,kgRawTensorUnit]

theorem kg_raw_symmetry (x : PureVector E) (y : PureVector F) :
    PureVector.mapUnitary (TensorProduct.commIsometry ℂ E F) (kgRawTensor x y) =
      kgRawTensor y x := by
  apply Subtype.ext
  simp [kgRawTensor]

theorem kg_raw_tensor_pentagon :
    (TensorProduct.assoc ℂ E F (G ⊗[ℂ] H)).toLinearMap.comp
      (TensorProduct.assoc ℂ (E ⊗[ℂ] F) G H).toLinearMap =
    (TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E)
      (TensorProduct.assoc ℂ F G H).toLinearMap).comp
      ((TensorProduct.assoc ℂ E (F ⊗[ℂ] G) H).toLinearMap.comp
        (TensorProduct.map (TensorProduct.assoc ℂ E F G).toLinearMap
          (LinearMap.id : H →ₗ[ℂ] H))) := by
  apply TensorProduct.ext_fourfold
  intro w x y z
  simp

theorem kg_raw_tensor_triangle :
    (TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E)
      (TensorProduct.lid ℂ F).toLinearMap).comp
        (TensorProduct.assoc ℂ E ℂ F).toLinearMap =
    TensorProduct.map (TensorProduct.rid ℂ E).toLinearMap (LinearMap.id : F →ₗ[ℂ] F) := by
  apply TensorProduct.ext_threefold
  intro x c y
  simp [TensorProduct.tmul_smul]
  exact (TensorProduct.smul_tmul' c x y).symm

theorem kg_raw_tensor_symmetry_involutive :
    (TensorProduct.comm ℂ F E).toLinearMap.comp
      (TensorProduct.comm ℂ E F).toLinearMap = LinearMap.id := by
  apply TensorProduct.ext'
  intro x y
  simp

theorem kg_raw_tensor_hexagon :
    (TensorProduct.assoc ℂ F G E).toLinearMap.comp
      ((TensorProduct.comm ℂ E (F ⊗[ℂ] G)).toLinearMap.comp
        (TensorProduct.assoc ℂ E F G).toLinearMap) =
    (TensorProduct.map (LinearMap.id : F →ₗ[ℂ] F)
      (TensorProduct.comm ℂ E G).toLinearMap).comp
      ((TensorProduct.assoc ℂ F E G).toLinearMap.comp
        (TensorProduct.map (TensorProduct.comm ℂ E F).toLinearMap
          (LinearMap.id : G →ₗ[ℂ] G))) := by
  apply TensorProduct.ext_threefold
  intro x y z
  simp

end AASCKleinGordon
