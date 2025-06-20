import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2

section mkContinuous₂

namespace LinearMap

variable {E F G 𝕜 : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedAddCommGroup G] [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] (f : E →ₗ[𝕜] F →ₗ[𝕜] G)

/-- Given a biliniear map whose codomains are finite dimensional, outputs the continuous
version. -/
def mkContinuous₂OfFiniteDimensional : E →L[𝕜] F →L[𝕜] G :=
  letI g x : F →L[𝕜] G := (f x).toContinuousLinearMap
  letI h : E →ₗ[𝕜] F →L[𝕜] G :=
    { toFun := g
      map_add' x y := by ext z; simp [g]
      map_smul' m x := by ext y; simp [g] }
  h.toContinuousLinearMap

@[simp]
lemma mkContinuous₂OfFiniteDimensional_apply (x : E) (y : F) :
    f.mkContinuous₂OfFiniteDimensional x y = f x y := rfl

end LinearMap

end mkContinuous₂

section InnerProductSpace

open scoped InnerProductSpace

lemma OrthonormalBasis.inner_eq {𝕜 E ι : Type*} [NormedAddCommGroup E] [RCLike 𝕜]
    [InnerProductSpace 𝕜 E] [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) {i j : ι} :
    ⟪b i, b j⟫_𝕜 = if i = j then 1 else 0 := by
  by_cases h : i = j
  · simp only [h, ↓reduceIte]
    apply RCLike.ext
    · simp [inner_self_eq_norm_sq]
    · simp
  · simp [h]

theorem OrthonormalBasis.sum_sq_inner_right {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x : E) :
    ∑ i : ι, ⟪b i, x⟫_ℝ ^ 2 = ‖x‖ ^ 2 := by
  rw [← b.sum_sq_norm_inner]
  simp

theorem OrthonormalBasis.sum_sq_inner_left {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x : E) :
    ∑ i : ι, ⟪x, b i⟫_ℝ ^ 2 = ‖x‖ ^ 2 := by
  simp_rw [← b.sum_sq_inner_right, real_inner_comm]

@[simp]
lemma inner_toDual_symm_eq_self {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (L : NormedSpace.Dual 𝕜 E) :
  inner 𝕜 ((InnerProductSpace.toDual 𝕜 E).symm L) = L := by ext; simp

theorem OrthonormalBasis.norm_dual {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype ι] (b : OrthonormalBasis ι ℝ E) (L : NormedSpace.Dual ℝ E) :
    ‖L‖ ^ 2 = ∑ i, L (b i) ^ 2 := by
  have := FiniteDimensional.of_fintype_basis b.toBasis
  simp_rw [← (InnerProductSpace.toDual ℝ E).symm.norm_map, ← b.sum_sq_inner_left,
    InnerProductSpace.toDual_symm_apply]

lemma LinearIsometryEquiv.coe_coe_eq_coe {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] (f : E ≃ₗᵢ[𝕜] F) :
    f.toLinearIsometry.toContinuousLinearMap = (f : E →L[𝕜] F) := rfl

end InnerProductSpace
