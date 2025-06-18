import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Measure theory lemmas to be upstreamed to Mathlib
-/

open MeasureTheory

open scoped NNReal ProbabilityTheory

namespace ProbabilityTheory

@[simp]
lemma charFun_toDual_symm_eq_charFunDual {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [InnerProductSpace ℝ E] {mE : MeasurableSpace E} {μ : Measure E} (L : NormedSpace.Dual ℝ E) :
    charFun μ ((InnerProductSpace.toDual ℝ E).symm L) = charFunDual μ L := by
  rw [charFun_eq_charFunDual_toDualMap]
  congr with x
  simp

@[simp]
lemma inner_toDual_symm_eq_self {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (L : NormedSpace.Dual 𝕜 E) :
  inner 𝕜 ((InnerProductSpace.toDual 𝕜 E).symm L) = L := by ext; simp

lemma eq_gaussianReal_integral_variance {μ : Measure ℝ} {m : ℝ} {v : ℝ≥0}
    (h : μ = gaussianReal m v) : μ = gaussianReal μ[id] Var[id; μ].toNNReal := by
  simp [h]

section iIndepFun

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]

lemma measurePreserving_eval (i : ι) :
    MeasurePreserving (Function.eval i) (Measure.pi μ) (μ i) := by
  refine ⟨measurable_pi_apply i, ?_⟩
  ext s hs
  classical
  rw [Measure.map_apply (measurable_pi_apply i) hs, ← Set.univ_pi_update_univ, Measure.pi_pi]
  have : μ i s = (μ i) (Function.update (fun j ↦ Set.univ) i s i) := by simp
  rw [this]
  exact Finset.prod_eq_single_of_mem i (by simp) (fun j _ hj ↦ by simp [hj])

variable {𝒳 : ι → Type*} {m𝒳 : ∀ i, MeasurableSpace (𝒳 i)} {X : Π i, Ω i → 𝒳 i}

lemma iIndepFun_pi (mX : ∀ i, Measurable (X i)) :
    iIndepFun (fun i ω ↦ X i (ω i)) (Measure.pi μ) := by
  refine @iIndepFun_iff_map_fun_eq_pi_map (Π i, Ω i) ι _ (Measure.pi μ) _ 𝒳 _
    (fun i x ↦ X i (x i)) _ ?_ |>.2 ?_
  · exact fun i ↦ Measurable.aemeasurable (by fun_prop)
  · symm
    refine Measure.pi_eq fun s hs ↦ ?_
    rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
    have : (fun (ω : Π i, Ω i) i ↦ X i (ω i)) ⁻¹' (Set.univ.pi s) =
        Set.univ.pi (fun i ↦ (X i) ⁻¹' (s i)) := by ext x; simp
    rw [this, Measure.pi_pi]
    congr with i
    rw [Measure.map_apply (by fun_prop) (hs i)]
    change _ = (Measure.pi μ) (((X i) ∘ (fun x ↦ x i)) ⁻¹' s i)
    rw [Set.preimage_comp, ← Measure.map_apply (measurable_pi_apply i) (mX i (hs i)),
      (measurePreserving_eval i).map_eq]

lemma iIndepFun_pi₀ (mX : ∀ i, AEMeasurable (X i) (μ i)) :
    iIndepFun (fun i ω ↦ X i (ω i)) (Measure.pi μ) := by
  have : iIndepFun (fun i ω ↦ (mX i).mk (X i) (ω i)) (Measure.pi μ) :=
    iIndepFun_pi fun i ↦ (mX i).measurable_mk
  refine this.congr fun i ↦ ?_
  change ((mX i).mk (X i)) ∘ Function.eval i =ᶠ[_] (X i) ∘ Function.eval i
  apply ae_eq_comp
  · exact (measurable_pi_apply i).aemeasurable
  · rw [(measurePreserving_eval i).map_eq]
    exact (AEMeasurable.ae_eq_mk (mX i)).symm

lemma variance_pi {X : Π i, Ω i → ℝ} (h : ∀ i, MemLp (X i) 2 (μ i)) :
    Var[∑ i, fun ω ↦ X i (ω i); Measure.pi μ] = ∑ i, Var[X i; μ i] := by
  rw [IndepFun.variance_sum]
  · congr with i
    change Var[(X i) ∘ (fun ω ↦ ω i); Measure.pi μ] = _
    rw [← variance_map, (measurePreserving_eval i).map_eq]
    · rw [(measurePreserving_eval i).map_eq]
      exact (h i).aestronglyMeasurable.aemeasurable
    · exact Measurable.aemeasurable (by fun_prop)
  · exact fun i _ ↦ (h i).comp_measurePreserving (measurePreserving_eval i)
  · exact fun i _ j _ hij ↦
      (iIndepFun_pi₀ fun i ↦ (h i).aestronglyMeasurable.aemeasurable).indepFun hij

end iIndepFun

end ProbabilityTheory

lemma _root_.ContinuousLinearMap.integral_comp_id_comm' {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
    [NormedSpace 𝕜 F] [NormedSpace ℝ F] [CompleteSpace E] [CompleteSpace F] [MeasurableSpace E]
    [OpensMeasurableSpace E] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {μ : Measure E} (h : Integrable id μ) (L : E →L[𝕜] F) : μ[L] = L μ[id] := by
  change ∫ x, L (id x) ∂μ = _
  rw [L.integral_comp_comm h]

lemma _root_.ContinuousLinearMap.integral_comp_id_comm {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
    [NormedSpace 𝕜 F] [NormedSpace ℝ F] [CompleteSpace E] [CompleteSpace F] [MeasurableSpace E]
    [OpensMeasurableSpace E] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {μ : Measure E} (h : Integrable id μ) (L : E →L[𝕜] F) : μ[L] = L (∫ x, x ∂μ) :=
  L.integral_comp_id_comm' h

lemma _root_.ContinuousLinearMap.integral_id_map {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
    [NormedSpace 𝕜 F] [NormedSpace ℝ F] [CompleteSpace E] [CompleteSpace F] [MeasurableSpace E]
    [OpensMeasurableSpace E] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {μ : Measure E} (h : Integrable id μ) (L : E →L[𝕜] F) : (μ.map L)[id] = L μ[id] := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp [L.integral_comp_id_comm h]
