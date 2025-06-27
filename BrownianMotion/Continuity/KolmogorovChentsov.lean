/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Continuity.HasBoundedInternalCoveringNumber
import BrownianMotion.Continuity.IsKolmogorovProcess

/-!
# Kolmogorov-Chentsov theorem

-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section aux

theorem lintegral_eq_zero_of_zero_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} : f =ᵐ[μ] 0 →  ∫⁻ a, f a ∂μ = 0 :=
  fun h ↦ (lintegral_congr_ae h).trans lintegral_zero

-- copied from Etienne's fork
theorem measurable_limUnder {ι X E : Type*} [MeasurableSpace X] [TopologicalSpace E] [PolishSpace E]
    [MeasurableSpace E] [BorelSpace E] [Countable ι] {l : Filter ι}
    [l.IsCountablyGenerated] {f : ι → X → E} [hE : Nonempty E] (hf : ∀ i, Measurable (f i)) :
    Measurable (fun x ↦ limUnder l (f · x)) := by
  obtain rfl | hl := eq_or_neBot l
  · simp [limUnder, Filter.map_bot]
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable
  let e := Classical.choice hE
  let conv := {x | ∃ c, Tendsto (f · x) l (𝓝 c)}
  have mconv : MeasurableSet conv := measurableSet_exists_tendsto hf
  have : (fun x ↦ _root_.limUnder l (f · x)) = ((↑) : conv → X).extend
      (fun x ↦ _root_.limUnder l (f · x)) (fun _ ↦ e) := by
    ext x
    by_cases hx : x ∈ conv
    · rw [Function.extend_val_apply hx]
    · rw [Function.extend_val_apply' hx, limUnder_of_not_tendsto hx]
  rw [this]
  refine (MeasurableEmbedding.subtype_coe mconv).measurable_extend
    (measurable_of_tendsto_metrizable' l
      (fun i ↦ (hf i).comp measurable_subtype_coe)
      (tendsto_pi_nhds.2 fun ⟨x, ⟨c, hc⟩⟩ ↦ ?_)) measurable_const
  rwa [hc.limUnder_eq]

lemma _root_.MeasureTheory.Measure.measure_inter_eq_of_measure_eq_measure_univ
    {α : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    {s t : Set α} (hs : MeasurableSet s) (h : μ t = μ .univ)
    (ht_ne_top : μ t ≠ ∞) : μ (t ∩ s) = μ s := by
  rw [Measure.measure_inter_eq_of_measure_eq hs h (Set.subset_univ _) ht_ne_top, Set.univ_inter]

lemma _root_.MeasureTheory.Measure.measure_inter_eq_of_ae
    {α : Type*} {_ : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]
    {s t : Set α} (hs : MeasurableSet s) (ht : NullMeasurableSet t μ) (h : ∀ᵐ a ∂μ, a ∈ t)
    (ht_ne_top : μ t ≠ ∞) : μ (t ∩ s) = μ s := by
  rw [Measure.measure_inter_eq_of_measure_eq hs _ (Set.subset_univ _) ht_ne_top, Set.univ_inter]
  rwa [ae_iff_measure_eq] at h
  exact ht

end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} [PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω}
  {X : T → Ω → E} {c : ℝ≥0∞} {d p q : ℝ} {M β : ℝ≥0} {P : Measure Ω}

section PseudoEMetricSpace

variable [PseudoEMetricSpace E] [MeasurableSpace E] [BorelSpace E]

lemma lintegral_div_edist_le_sum_integral_edist_le (hT : EMetric.diam (Set.univ : Set T) < ∞)
    (hX : IsKolmogorovProcess X P p q M)
    (hβ : 0 < β) (hp : 0 < p) (hq : 0 < q) {J : Set T} [hJ : Countable J] :
    ∫⁻ ω, ⨆ (s : J) (t : J), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) ∂P
      ≤ ∑' (k : ℕ), 2 ^ (k * β * p)
          * ∫⁻ ω, ⨆ (s : J)
              (t : {t : J // edist s t ≤ 2 * 2⁻¹ ^ k * (EMetric.diam (.univ : Set T) + 1)}),
                edist (X s ω) (X t ω) ^p ∂P := by
  let η k := 2⁻¹ ^ k * (EMetric.diam (Set.univ : Set T) + 1)
  have hη_ge (k : ℕ) : 2⁻¹ ^ (k : ℝ) ≤ η k := by simp [η, mul_add]
  have hη_succ (k : ℕ) : η (k + 1) = 2⁻¹ * η k := by simp [η, pow_add, mul_assoc, mul_comm]
  have hη_lim : Filter.Tendsto η Filter.atTop (nhds 0) := by
    unfold η
    rw [← zero_mul (EMetric.diam (Set.univ : Set T) + 1)]
    apply ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num))
    simp [← lt_top_iff_ne_top, hT]
  conv in 2 ^ _ * _ => rw [← lintegral_const_mul' _ _ (by simp)]
  rw [← lintegral_tsum (by fun_prop (disch := exact hX))]
  have h_ae : ∀ᵐ (ω : Ω) ∂P, ∀ (s t : J), edist s t = 0 → edist (X s ω) (X t ω) = 0 := by
    rw [eventually_countable_forall]; intro s
    rw [eventually_countable_forall]; intro t
    by_cases h_dist : edist s t = 0
    · apply Filter.Eventually.mp (IsKolmogorovProcess.edist_eq_zero hX hp hq h_dist)
      filter_upwards with _ h _ using h
    filter_upwards with _ using by simp [h_dist]
  refine lintegral_mono_ae (Filter.Eventually.mp h_ae ?_)
  filter_upwards with ω h
  rw [iSup_le_iff]; rintro ⟨s, hs⟩
  rw [iSup_le_iff]; intro ⟨t, ht⟩
  wlog hst : 0 < edist s t
  · simp [(h ⟨s, hs⟩ ⟨t, ht⟩) <| nonpos_iff_eq_zero.mp (le_of_not_gt hst),
      ENNReal.zero_rpow_of_pos (by positivity)]
  obtain ⟨k, lb, ub⟩ : ∃ k, (η k ≤ edist s t) ∧ (edist s t ≤ 2 * η k) := by
    have hη_dist : ∃ k, η k ≤ edist s t :=
      (Filter.Eventually.exists (Filter.Tendsto.eventually_le_const hst hη_lim))
    refine ⟨Nat.find hη_dist, Nat.find_spec hη_dist, ?_⟩
    match hk : Nat.find hη_dist with
    | 0 =>
        apply le_trans (EMetric.edist_le_diam_of_mem (Set.mem_univ _) (Set.mem_univ _))
        simp [η]
        exact le_mul_of_one_le_of_le (by norm_num) (le_add_right (le_refl _))
    | k + 1 =>
        rw [hη_succ k, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
        refine le_of_not_ge (Nat.find_min hη_dist ?_)
        simp [hk]
  refine le_trans ?_ (Summable.le_tsum (ENNReal.summable) k (fun _ _ ↦ zero_le _))
  rw [ENNReal.div_eq_inv_mul]
  refine mul_le_mul ?_ ?_ (zero_le _) (zero_le _)
  · rw [ENNReal.inv_le_iff_inv_le, ← ENNReal.inv_rpow, mul_assoc, ENNReal.rpow_mul,
      ENNReal.rpow_le_rpow_iff (by positivity)]
    exact le_trans (hη_ge k) lb
  apply le_iSup_of_le (i := ⟨s, hs⟩)
  exact le_iSup_of_le (i := ⟨⟨t, ht⟩, by rwa [mul_assoc]⟩) (le_refl _)

noncomputable
-- the `max 0 ...` in the blueprint is performed by `ENNReal.ofReal` here
def constL (T : Type*) [PseudoEMetricSpace T] (c : ℝ≥0∞) (d p q β : ℝ) : ℝ≥0∞ :=
  2 ^ (2 * p + 5 * q + 1) * c * (EMetric.diam (.univ : Set T) + 1) ^ (q - d)
  * ∑' (k : ℕ), 2 ^ (k * (β * p - (q - d)))
      * (4 ^ d * (ENNReal.ofReal (Real.logb 2 c.toReal + (k + 2) * d)) ^ q
        + Cp d p q)

lemma constL_lt_top (hc : c ≠ ∞) (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p) :
    constL T c d p q β < ∞ := by
  sorry

theorem finite_kolmogorov_chentsov
    (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p) (T' : Set T) [hT' : Finite T'] :
    ∫⁻ ω, ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) ∂P
      ≤ M * constL T c d p q β := by
  have h_diam : EMetric.diam .univ < ∞ := hT.diam_lt_top hd_pos
  have hq_pos : 0 < q := lt_trans hd_pos hdq_lt
  simp [constL, ← ENNReal.tsum_mul_left]
  by_cases h_ae : ∀ᵐ (ω : Ω) ∂P, ∀ (s t : T'), edist (X s ω) (X t ω) = 0
  · convert zero_le'
    apply lintegral_eq_zero_of_zero_ae
    filter_upwards [h_ae] with ω h
    rw [Pi.zero_apply]
    rw [ENNReal.iSup_eq_zero]; rintro ⟨s, hs⟩
    rw [ENNReal.iSup_eq_zero]; rintro ⟨t, ht⟩
    simp [h ⟨s, hs⟩ ⟨t, ht⟩, hp_pos]
  have hM : (M : ℝ≥0∞) ≠ 0 := by
    contrapose! h_ae
    rw [Filter.eventually_all]; intro s
    rw [Filter.eventually_all]; intro t
    rw_mod_cast [h_ae] at hX
    exact hX.edist_eq_zero_of_M_eq_zero hp_pos
  have h_diam_zero : 0 < EMetric.diam (.univ : Set T) := by
    contrapose! h_ae
    rw [Filter.eventually_all]; intro s
    rw [Filter.eventually_all]; intro t
    apply hX.edist_eq_zero hp_pos hq_pos
    rw [← le_zero_iff]
    exact le_trans (EMetric.edist_le_diam_of_mem (Set.mem_univ _) (Set.mem_univ _)) h_ae
  have h_diam_real : 0 < (EMetric.diam (.univ : Set T)).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨h_diam_zero, h_diam⟩
  apply le_trans (lintegral_div_edist_le_sum_integral_edist_le h_diam hX hβ_pos hp_pos hq_pos)
  apply ENNReal.tsum_le_tsum
  intro k
  wlog hc : c ≠ ∞
  · simp [not_ne_iff.mp hc]
    repeat rw [ENNReal.top_mul]
    · rw [ENNReal.mul_top hM]
      exact le_top
    · have : 0 < (k + 2) * d := by positivity
      simp [this]
    · simp [le_of_lt hdq_lt]
  apply le_trans
  · apply mul_le_mul_left'
    refine finite_set_bound_of_edist_le (c := 2 ^ d * c) ?_ hT' hX ?_ hd_pos hp_pos hdq_lt ?_
    · exact hT.subset (Set.subset_univ _) hd_pos.le
    · finiteness
    · simp
  rw [ENNReal.mul_rpow_of_ne_top (by finiteness) (by finiteness), ← mul_assoc,
    ← mul_assoc _ (2 ^ ((k : ℝ) * _)), ← mul_assoc (M : ℝ≥0∞)]
  refine mul_le_mul' (le_of_eq ?_) ?_
  · calc 2 ^ (k * β * p) * (2 ^ (2 * p + 4 * q + 1) * M * (2 ^ d * c)
        * ((2 * 2⁻¹ ^ k) ^ (q - d) * (EMetric.diam Set.univ + 1) ^ (q - d)))
    _ = 2 ^ (k * β * p) * (2 ^ (2 * p + 4 * q + 1) * M * (2 ^ d * c)
        * ((2 ^ (q - d) * 2 ^ (- k * (q - d)))
        * (EMetric.diam (Set.univ : Set T) + 1) ^ (q - d))) := by
      congr
      rw [ENNReal.rpow_mul, ENNReal.mul_rpow_of_nonneg _ _ (by bound), ENNReal.rpow_neg,
        ← ENNReal.inv_pow, ENNReal.rpow_natCast]
    _ = M * (2 ^ (2 * p + 4 * q + 1) * (2 ^ (q - d) * 2 ^ d)) * c
        * (EMetric.diam (Set.univ : Set T) + 1) ^ (q - d)
        * (2 ^ (k * β * p) * 2 ^ (- k * (q - d))) := by ring
    _ = M * 2 ^ (2 * p + 5 * q + 1) * c * (EMetric.diam Set.univ + 1) ^ (q - d)
        * 2 ^ (↑k * (↑β * p - (q - d))) := by
      congr
      · rw [← ENNReal.rpow_add _ _ (by simp) (by simp), ← ENNReal.rpow_add _ _ (by simp) (by simp)]
        ring_nf
      · rw [← ENNReal.rpow_add _ _ (by simp) (by simp)]
        ring_nf
    _ = _ := by ring
  by_cases hc_zero : c.toReal = 0
  · simp [hc_zero]; gcongr; exact zero_le _
  gcongr with k
  simp only [← ENNReal.rpow_natCast, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, mul_inv_rev]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  repeat rw [Real.mul_rpow (by positivity) (by positivity)]
  repeat rw [Real.logb_mul (by positivity) (by positivity)]
  grw [inv_lt_one_of_one_lt₀ (by simp [h_diam_real])]
  · apply le_of_eq
    rw [(by norm_num : (4 : ℝ) = 2 ^ (2 : ℝ)), ← Real.inv_rpow (by positivity), inv_inv,
      ← Real.rpow_neg_one]
    repeat rw [← Real.rpow_mul (by positivity)]
    repeat rw [Real.logb_rpow (by norm_num) (by norm_num)]
    simp
    ring
  · norm_num

theorem countable_kolmogorov_chentsov (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p)
    (T' : Set T) (hT' : T'.Countable) :
    ∫⁻ ω, ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) ∂P
      ≤ M * constL T c d p q β := by
  sorry

end PseudoEMetricSpace

section EMetricSpace

variable [EMetricSpace E] [MeasurableSpace E] [BorelSpace E]

lemma ae_iSup_rpow_edist_div_lt_top (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsMeasurableKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p)
    {T' : Set T} (hT' : T'.Countable) :
    ∀ᵐ ω ∂P, ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) < ∞ := by
  have : Countable T' := hT'
  refine ae_lt_top' ?_ ((countable_kolmogorov_chentsov hT hX.IsKolmogorovProcess hd_pos hp_pos
    hdq_lt hβ_pos hβ_lt T' hT').trans_lt ?_).ne
  · refine AEMeasurable.iSup (fun s ↦ AEMeasurable.iSup (fun t ↦ ?_))
    exact AEMeasurable.div (hX.measurable_edist.aemeasurable.pow_const _) (by fun_prop)
  · exact ENNReal.mul_lt_top (by simp) (constL_lt_top hc hd_pos hp_pos hdq_lt hβ_pos hβ_lt)

omit [MeasurableSpace E] [BorelSpace E] in
def holderSet (X : T → Ω → E) (T' : Set T) (p β : ℝ) : Set Ω :=
  {ω | ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) < ∞
      ∧ ∀ (s t : T'), edist s t = 0 → edist (X s ω) (X t ω) = 0}

omit [MeasurableSpace E] [BorelSpace E] in
lemma measurableSet_holderSet (hX : IsMeasurableKolmogorovProcess X P p q M)
    {T' : Set T} (hT' : T'.Countable) :
    MeasurableSet (holderSet X T' p β) := by
  have : Countable T' := hT'
  let C ω := ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p)
  refine MeasurableSet.inter ?_ ?_
  · change MeasurableSet {ω | C ω < ∞}
    refine measurableSet_lt ?_ (by fun_prop)
    refine Measurable.iSup (fun s ↦ Measurable.iSup (fun t ↦ ?_))
    exact Measurable.div (hX.measurable_edist.pow_const _) (by fun_prop)
  · have : {ω | ∀ (s t : T'), edist s t = 0 → edist (X s ω) (X t ω) = 0}
        = ⋂ (s : T') (t : T'), ({ω | edist (X s ω) (X t ω) = 0} ∪ {ω | edist s t ≠ 0}) := by
      ext; simp [imp_iff_or_not]
    change MeasurableSet {ω | ∀ (s t : T'), edist s t = 0 → edist (X s ω) (X t ω) = 0}
    rw [this]
    refine MeasurableSet.iInter (fun s ↦ MeasurableSet.iInter (fun t ↦ ?_))
    refine MeasurableSet.union ?_ ?_
    · exact MeasurableSet.preimage (measurableSet_singleton 0) hX.measurable_edist
    · exact (MeasurableSet.preimage (measurableSet_singleton 0) (by fun_prop)).compl

omit [MeasurableSpace E] [BorelSpace E] in
lemma holder_with_X (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hβ_pos : 0 < β)
    {T' : Set T} {ω : Ω} (hω : ω ∈ holderSet X T' p β) :
    letI C ω := ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p)
    HolderWith (C ω ^ p⁻¹).toNNReal β fun (t : T') ↦ X t ω := by
  intro s t
  have h_edist_lt_top : edist s t < ∞ := by
    calc edist s t ≤ EMetric.diam (Set.univ : Set T) :=
      EMetric.edist_le_diam_of_mem (Set.mem_univ s) (Set.mem_univ t)
    _ < ∞ := hT.diam_lt_top hd_pos
  have h_dist_top : edist s t ^ (β : ℝ) ≠ ∞
  · simp only [ne_eq, ENNReal.rpow_eq_top_iff, NNReal.coe_pos, not_or, not_and, not_lt,
      NNReal.zero_le_coe, implies_true, nonpos_iff_eq_zero, true_and]
    exact fun h_eq_top ↦ absurd h_eq_top h_edist_lt_top.ne
  by_cases h_dist_zero : edist s t = 0
  · simpa [h_dist_zero, hβ_pos] using hω.2 s t h_dist_zero
  rw [← ENNReal.div_le_iff (by simp [h_dist_zero]) h_dist_top]
  rw [ENNReal.coe_toNNReal]
  swap; · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hω.1.ne
  rw [ENNReal.le_rpow_inv_iff hp_pos, ENNReal.div_rpow_of_nonneg _ _ hp_pos.le,
    ← ENNReal.rpow_mul]
  exact le_iSup₂ s t (f := fun (s t : T') ↦ edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p))

lemma _root_.Dense.holderWith_extend {A : Set T} (hA : Dense A) {f : A → E} {C β : ℝ≥0}
    (hf : HolderWith C β f) :
    HolderWith C β (hA.extend f) := by
  sorry

-- TODO: I (Rémy) gave up on separability of `E`. The measurability checks are driving me crazy.
variable [Nonempty E] [SecondCountableTopology T] [CompleteSpace E] [SecondCountableTopology E]
  [IsFiniteMeasure P]

-- TODO: in this lemma we use the notion of convergence in measure, but since we use `edist` and not
-- `dist`, we can't use the existing definition `TendstoInMeasure`.
lemma exists_modification_holder_aux' (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsMeasurableKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ ω, ∃ C : ℝ≥0, HolderWith C β (Y · ω) := by
  -- Let `T'` be a countable dense subset of `T`
  obtain ⟨T', hT'_countable, hT'_dense⟩ := TopologicalSpace.exists_countable_dense T
  have : Countable T' := hT'_countable
  have h_ae_zero : ∀ᵐ ω ∂P, ∀ (s t : T'), edist s t = 0 → edist (X s ω) (X t ω) = 0 := by
    simp_rw [ae_all_iff]
    exact fun s t hst ↦ hX.IsKolmogorovProcess.edist_eq_zero hp_pos (hd_pos.trans hdq_lt) hst
  -- For each `ω`, `C ω < ∞` is a bound on `edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p)`
  let C ω := ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p)
  have hC_lt_top : ∀ᵐ ω ∂P, C ω < ∞ :=
    ae_iSup_rpow_edist_div_lt_top hT hX hc hd_pos hp_pos hdq_lt hβ_pos hβ_lt hT'_countable
  -- Let `A` be the event that `C ω < ∞` and `X s ω = X t ω` for `edist s t = 0`.
  -- This is an event of probability 1.
  let A := holderSet X T' p β
  have hA : MeasurableSet A := measurableSet_holderSet hX hT'_countable
  have hA_ae : ∀ᵐ ω ∂P, ω ∈ A := by
    filter_upwards [hC_lt_top, h_ae_zero] with ω hω₁ hω₂ using ⟨hω₁, hω₂⟩
  have h_holder {ω} (hω : ω ∈ A) : HolderWith (C ω ^ p⁻¹).toNNReal β fun (t : T') ↦ X t ω :=
    holder_with_X hT hd_pos hp_pos hβ_pos hω
  have h_cont {ω} (hω : ω ∈ A) : Continuous fun (t : T') ↦ X t ω := (h_holder hω).continuous hβ_pos
  let x₀ : E := Nonempty.some inferInstance
  classical
  let Y (t : T) (ω : Ω) : E := if ω ∈ A then hT'_dense.extend (fun t ↦ X t ω) t else x₀
  have hY t : Measurable (Y t) := by
    refine Measurable.ite hA ?_ (by fun_prop)
    -- todo: extract lemma `measurable_extend`
    exact measurable_limUnder (f := fun (t : T') ω ↦ X t ω) fun t ↦ hX.measurable t
  have hY_eq {ω : Ω} (hω : ω ∈ A) (t : T') : Y t ω = X t ω := by
    simp only [hω, ↓reduceIte, Y]
    exact hT'_dense.extend_eq (h_cont hω) t
  refine ⟨Y, hY, fun t ↦ ?_, fun ω ↦ ?_⟩
  · suffices ∀ᵐ ω ∂P, edist (Y t ω) (X t ω) ≤ 0 by
      filter_upwards [this] with ω h using by simpa using h
    obtain ⟨u, hu⟩ : ∃ u : ℕ → T', Tendsto (fun n ↦ (u n : T)) atTop (𝓝 t) := by
      have ht_mem_closure : t ∈ closure T' := by simp [hT'_dense.closure_eq]
      rw [mem_closure_iff_seq_limit] at ht_mem_closure
      obtain ⟨u, hu⟩ := ht_mem_closure
      exact ⟨fun n ↦ ⟨u n, hu.1 n⟩, hu.2⟩
    have h_le n {ω} (hω : ω ∈ A) : edist (Y t ω) (X t ω)
        ≤ edist (Y t ω) (Y (u n) ω) + edist (X (u n) ω) (X t ω) := by
      refine (edist_triangle4 (Y t ω) (Y (u n) ω) (X (u n) ω) (X t ω)).trans_eq ?_
      simp [hY_eq hω (u n)]
    -- `X (u n)` converges in measure to `X t`
    have h_tendsto_X (ε : ℝ≥0∞) (hε : 0 < ε) :
        Tendsto (fun n ↦ P {ω | ε ≤ edist (X (u n) ω) (X t ω)}) atTop (𝓝 0) := by
      have h_tendsto : Tendsto (fun n ↦ ∫⁻ ω, edist (X (u n) ω) (X t ω) ^ p ∂P) atTop (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le')
          (fun n ↦ hX.kolmogorovCondition (u n) t)
        have : Tendsto (fun n ↦ edist (u n).1 t) atTop (𝓝 0) := by
          rwa [← tendsto_iff_edist_tendsto_0]
        sorry -- no problem
      sorry -- go to `... ^ p`, use Markov and `h_tendsto`
    -- `Y (u n)` converges in measure to `Y t`
    have h_tendsto_Y (ε : ℝ≥0∞) (hε : 0 < ε) :
        Tendsto (fun n ↦ P {ω | ε ≤ edist (Y (u n) ω) (Y t ω)}) atTop (𝓝 0) := by
      sorry -- why?
    refine (ae_le_const_iff_forall_gt_measure_zero _ _).mpr fun ε hε ↦ ?_
    suffices Tendsto (fun n : ℕ ↦ P {ω | ε ≤ edist (Y t ω) (X t ω)}) atTop (𝓝 0) by
      simpa using this
    have hP_le n : P {ω | ε ≤ edist (Y t ω) (X t ω)}
        ≤ P {ω | ε/2 ≤ edist (Y (u n) ω) (Y t ω)} + P {ω | ε/2 ≤ edist (X (u n) ω) (X t ω)} := by
      calc P {ω | ε ≤ edist (Y t ω) (X t ω)}
      _ = P ({ω | ε ≤ edist (Y t ω) (X t ω)} ∩ A) := by
        rw [Set.inter_comm,
          Measure.measure_inter_eq_of_ae _ hA.nullMeasurableSet hA_ae (measure_ne_top _ _)]
        exact measurableSet_le (by fun_prop) (Measurable.edist (hY t) (hX.measurable t))
      _ ≤ P ({ω | ε ≤ edist (Y (u n) ω) (Y t ω) + edist (X (u n) ω) (X t ω)} ∩ A) := by
        refine measure_mono fun ω ↦ ?_
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_imp]
        refine fun hε_le hω ↦ ⟨(hε_le.trans (h_le n hω)).trans_eq ?_, hω⟩
        rw [edist_comm]
      _ = P {ω | ε / 2 + ε / 2 ≤ edist (Y (u n) ω) (Y t ω) + edist (X (u n) ω) (X t ω)} := by
        simp only [ENNReal.add_halves]
        rw [Set.inter_comm, Measure.measure_inter_eq_of_ae _ hA.nullMeasurableSet hA_ae
          (measure_ne_top _ _)]
        refine measurableSet_le (by fun_prop) ?_
        exact ((hY (u n)).edist (hY t)).add ((hX.measurable (u n)).edist (hX.measurable t))
      _ ≤ P ({ω | ε / 2 ≤ edist (Y (u n) ω) (Y t ω)}
          ∪ {ω | ε / 2 ≤ edist (X (u n) ω) (X t ω)}) := by
          gcongr
          intro ω
          simp only [ENNReal.add_halves, Set.mem_setOf_eq, Set.mem_union]
          contrapose!
          intro ⟨h1, h2⟩
          calc _
          _ < ε / 2 + ε / 2 := by gcongr
          _ = ε := by simp
      _ ≤ P {ω | ε / 2 ≤ edist (Y (u n) ω) (Y t ω)}
          + P {ω | ε / 2 ≤ edist (X (u n) ω) (X t ω)} := measure_union_le _ _
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le') hP_le
    rw [← add_zero (0 : ℝ≥0∞)]
    exact Tendsto.add (h_tendsto_Y (ε / 2) (ENNReal.half_pos hε.ne'))
      (h_tendsto_X (ε / 2) (ENNReal.half_pos hε.ne'))
  · by_cases hω : ω ∈ A
    swap; · simp only [hω, ↓reduceIte, Y]; exact ⟨0, by simp [HolderWith]⟩
    simp only [hω, ↓reduceIte, Y, A]
    refine ⟨(C ω ^ p⁻¹).toNNReal, ?_⟩
    refine hT'_dense.holderWith_extend (h_holder hω)

lemma exists_modification_holder_aux (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hc : c ≠ ∞)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p) :
    ∃ Y : T → Ω → E, (∀ t, Y t =ᵐ[P] X t) ∧ ∀ ω, ∃ C : ℝ≥0, HolderWith C β (Y · ω) := by
  sorry

lemma exists_modification_holder (hT : HasBoundedInternalCoveringNumber (Set.univ : Set T) c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q) :
    ∃ Y : T → Ω → E, (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ (β : ℝ≥0) (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p),
        ∀ ω, ∃ C : ℝ≥0, HolderWith C β (Y · ω) := by
  sorry

lemma exists_modification_holder' {C : ℕ → Set T} {c : ℕ → ℝ≥0∞}
    (hC : IsCoverWithBoundedCoveringNumber C (Set.univ : Set T) c (fun _ ↦ d))
    (hX : IsKolmogorovProcess X P p q M) (hp_pos : 0 < p) (hdq_lt : d < q) :
    ∃ Y : T → Ω → E, (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ (β : ℝ≥0) (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p),
        ∀ ω, ∃ C : ℝ≥0, HolderWith C β (Y · ω) := by
  sorry

lemma exists_modification_holder_iSup {C : ℕ → Set T} {c : ℕ → ℝ≥0∞} {p q : ℕ → ℝ} {M : ℕ → ℝ≥0}
    (hC : IsCoverWithBoundedCoveringNumber C (Set.univ : Set T) c (fun _ ↦ d))
    (hX : ∀ n, IsKolmogorovProcess X P (p n) (q n) (M n))
    (hp_pos : ∀ n, 0 < p n) (hdq_lt : ∀ n, d < q n) :
    ∃ Y : T → Ω → E, (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ (β : ℝ≥0) (hβ_pos : 0 < β) (hβ_lt : β < ⨆ n, (q n - d) / (p n)),
        ∀ ω, ∃ C : ℝ≥0, HolderWith C β (Y · ω) := by
  sorry

end EMetricSpace

end ProbabilityTheory
