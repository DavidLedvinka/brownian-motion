import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Measure theory lemmas to be upstreamed to Mathlib
-/

open MeasureTheory

open scoped NNReal ProbabilityTheory

nonrec lemma _root_.ContinuousLinearMap.integral_id_map {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
    [NormedSpace 𝕜 F] [NormedSpace ℝ F] [CompleteSpace E] [CompleteSpace F] [MeasurableSpace E]
    [OpensMeasurableSpace E] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {μ : Measure E} (h : Integrable id μ) (L : E →L[𝕜] F) : (μ.map L)[id] = L μ[id] := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  change ∫ x, L (id x) ∂μ = _
  rw [L.integral_comp_comm h]
