import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open MeasureTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : T → Ω → E}

lemma modification_of_indistinduishable (h : ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω) :
    ∀ t, X t =ᵐ[P] Y t := by
  intro t
  filter_upwards [h] with ω hω using hω t

variable [MeasurableSpace E]

lemma finite_distributions_eq {I : Finset T} (h : ∀ t, X t =ᵐ[P] Y t) :
    P.map (fun ω ↦ I.restrict (X · ω)) = P.map (fun ω ↦ I.restrict (Y · ω)) := by
  have h' : ∀ᵐ ω ∂P, ∀ (i : I), X i ω = Y i ω := by
    rw [MeasureTheory.ae_all_iff]
    exact fun i ↦ h i
  refine Measure.map_congr ?_
  filter_upwards [h'] with ω h using funext fun i ↦ h i

theorem aemeasurable_proj {α δ : Type*} {X : δ → Type*} {mX : ∀ a, MeasurableSpace (X a)}
    [MeasurableSpace α] {μ : Measure α} {g : α → Π a, X a} (hg : AEMeasurable g μ) (a : δ) :
    AEMeasurable (fun x ↦ g x a) μ := by
  use fun x ↦ hg.mk g x a, hg.measurable_mk.eval
  exact hg.ae_eq_mk.mono fun _ h ↦ congrFun h _

lemma coincide_on_cylinders (hX : AEMeasurable (fun ω t ↦ X t ω) P)
    (hY : AEMeasurable (fun ω t ↦ Y t ω) P)
    (h : ∀ I : Finset T, P.map (fun ω ↦ I.restrict (X · ω)) = P.map (fun ω ↦ I.restrict (Y · ω)))
    (c : Set (T → E)) (hc : c ∈ measurableCylinders fun _ ↦ E) :
    P.map (fun ω t ↦ X t ω) c = P.map (fun ω t ↦ Y t ω) c := by
  rw [mem_measurableCylinders] at hc
  obtain ⟨s, S, hS, rfl⟩ := hc
  have hXtn : AEMeasurable (fun ω ↦ s.restrict (X · ω)) P :=
    aemeasurable_pi_lambda _ fun i ↦ (aemeasurable_proj hX) i
  have hYtn : AEMeasurable (fun ω ↦ s.restrict (Y · ω)) P :=
    aemeasurable_pi_lambda _ fun i ↦ (aemeasurable_proj hY) i
  have set1 : @MeasurableSet (T → E) MeasurableSpace.pi (s.restrict ⁻¹' S) :=
    Finset.measurable_restrict s hS
  have mappings_eq (XY : T → Ω → E) :
      (fun ω t ↦ XY t ω) ⁻¹' (s.restrict ⁻¹' S) = (fun ω ↦ s.restrict (XY · ω)) ⁻¹' S := by
    rw [← Set.preimage_comp]
    rfl
  have X_on_cyl : P.map (fun ω t ↦ X t ω) (s.restrict ⁻¹' S)
      = P.map (fun ω ↦ s.restrict (X · ω)) S := by
    rw [Measure.map_apply_of_aemeasurable hX set1, Measure.map_apply_of_aemeasurable hXtn hS,
      mappings_eq X]
  have Y_on_cyl : P.map (fun ω t ↦ Y t ω) (s.restrict ⁻¹' S)
      = P.map (fun ω ↦ s.restrict (Y · ω)) S := by
    rw [Measure.map_apply_of_aemeasurable hY set1, Measure.map_apply_of_aemeasurable hYtn hS,
      mappings_eq Y]
  rw [cylinder, X_on_cyl, Y_on_cyl, h]

lemma finite_distributions_eq_iff_same_law (hX : AEMeasurable (fun t ω ↦ X ω t) P)
    (hY : AEMeasurable (fun t ω ↦ Y ω t) P) [IsProbabilityMeasure P] :
    (∀ I : Finset T, P.map (fun ω ↦ I.restrict (X · ω)) = P.map (fun ω ↦ I.restrict (Y · ω)))
    ↔ (P.map (fun ω t ↦ X t ω) = P.map (fun ω t ↦ Y t ω)) := by
  constructor
  · intro h
    apply Measure.ext
    have pX : IsProbabilityMeasure (Measure.map (fun ω t ↦ X t ω) P) := isProbabilityMeasure_map hX
    have pY : IsProbabilityMeasure (Measure.map (fun ω t ↦ Y t ω) P) := isProbabilityMeasure_map hY
    apply MeasurableSpace.induction_on_inter
      (C := fun S hS ↦ ((P.map (fun ω t ↦ X t ω)) S = (P.map (fun ω t ↦ Y t ω)) S))
      (h_eq := by rw [generateFrom_measurableCylinders])
      (h_inter := isPiSystem_measurableCylinders)
      (empty := by simp) (basic := coincide_on_cylinders hX hY h)
    · intro t ht hXY
      repeat rw [MeasureTheory.prob_compl_eq_one_sub ht]
      simp [hXY]
    · intro f disj hf map
      repeat rw [measure_iUnion disj hf]
      simp [map]
  · intro h I
    have x : P.map (fun ω ↦ I.restrict (X · ω)) = (P.map (fun ω t ↦ X t ω)).map I.restrict := by
      rw [AEMeasurable.map_map_of_aemeasurable]; rfl
      · fun_prop
      · exact hX
    have y : P.map (fun ω ↦ I.restrict (Y · ω)) = (P.map (fun ω t ↦ Y t ω)).map I.restrict := by
      rw [AEMeasurable.map_map_of_aemeasurable]; rfl
      · fun_prop
      · exact hY
    rw [x, y, h]

open TopologicalSpace in
omit [MeasurableSpace E] in
lemma indistinduishable_of_modification [TopologicalSpace E] [TopologicalSpace T]
    [SeparableSpace T] [T2Space E]
    (hX : ∀ᵐ ω ∂P, Continuous fun t ↦ X t ω) (hY : ∀ᵐ ω ∂P, Continuous fun t ↦ Y t ω)
    (h : ∀ t, X t =ᵐ[P] Y t) :
    ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by
  let ⟨D, D_countable, D_dense⟩ := ‹SeparableSpace T›
  have eq (ht : ∀ t ∈ D, X t =ᵐ[P] Y t) : ∀ᵐ ω ∂P, ∀ t ∈ D, X t ω = Y t ω :=
    (ae_ball_iff D_countable).mpr ht
  filter_upwards [hX, hY, eq (fun t ht ↦ h t)] with ω hX hY h t
  show (fun t ↦ X t ω) t = (fun t ↦ Y t ω) t
  rw [Continuous.ext_on D_dense hX hY h]
