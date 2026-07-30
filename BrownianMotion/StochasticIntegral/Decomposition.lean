/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import BrownianMotion.StochasticIntegral.Jump
public import BrownianMotion.StochasticIntegral.LocalMartingale
public import BrownianMotion.StochasticIntegral.PredictableTime
public import BrownianMotion.StochasticIntegral.VariationProcess

@[expose] public section

open MeasureTheory ProbabilityTheory Function Filter
open scoped Topology

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} [NormedAddCommGroup E]
  [NormedSpace ℝ E] {P : Measure Ω} {X : ι → Ω → E} {ε : ℝ} {s t : ι}

section LinearOrder

variable [LinearOrder ι] {𝓕 : Filtration ι mΩ}

def largeJumpFinsetLe (f : ι → E) (ε : ℝ) (t : ι) : Finset ι := sorry

lemma mem_largeJumpFinsetLe {f : ι → E} : s ∈ largeJumpFinsetLe f ε t ↔
    s ≤ t ∧ ε < ‖Δ f s‖ := sorry

noncomputable def largeJumpProcess (X : ι → Ω → E) (ε : ℝ) (t : ι) (ω : Ω) : E :=
  ∑ s ∈ largeJumpFinsetLe (X · ω) ε t, Δ (X · ω) s

lemma largeJumpProcess_def : largeJumpProcess X ε t =
    fun ω ↦ ∑ s ∈ largeJumpFinsetLe (X · ω) ε t, Δ (X · ω) s := rfl

lemma measurable_jump [TopologicalSpace ι] [FirstCountableTopology ι] [OrderTopology ι]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] :
    Measurable (Δ · t : {f : ι → E // IsCadlag f} → E) := by
  by_cases h : Order.IsSuccLimit t
  · obtain ⟨u, mu, hu1, hu2, -⟩ := h.isLUB_Iio.exists_seq_strictMono_tendsto_of_notMem (by simp)
      h.nonempty_Iio
    rw [Order.isSuccLimit_iff, Order.IsSuccPrelimit] at h
    have : ¬ (∃ s, s ⋖ t) := by grind
    simp_rw [Function.jump, dif_neg this]
    have : Tendsto (fun n (x : {f : ι → E // IsCadlag f}) ↦ x.1 (u n)) atTop
        (𝓝 (fun x ↦ leftLim x t)) := by
      rw [tendsto_pi_nhds]
      rintro ⟨f, hf⟩
      refine tendsto_leftLim_of_tendsto (hf.left_limit t) |>.comp ?_
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact hu2
      · exact .of_forall hu1
    refine measurable_subtype_coe.eval.sub ?_
    apply measurable_of_tendsto_metrizable ?_ this
    exact fun _ ↦ measurable_subtype_coe.eval
  rw [Order.isSuccLimit_iff, Order.IsSuccPrelimit] at h
  push +distrib Not at h
  obtain h | h := h
  · simp [jump_of_isBot, h.isBot]
  · simp_rw [jump, dif_pos h]
    exact measurable_subtype_coe.eval.sub measurable_subtype_coe.eval

lemma test1 [TopologicalSpace ι] [FirstCountableTopology ι] [OrderTopology ι]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] :
    Measurable (fun f : {f : ι → E // IsCadlag f} ↦ ε < ‖Δ f.1 s‖) := by
  refine Measurable.lt measurable_const ?_
  exact measurable_norm.comp measurable_jump

lemma test2 [TopologicalSpace ι] [FirstCountableTopology ι] [OrderTopology ι]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] :
    Measurable (fun f : {f : ι → E // IsCadlag f} ↦ largeJumpFinsetLe f.1 ε t) := by
  simp_rw [measurable_finset_iff, mem_largeJumpFinsetLe]
  intro s
  refine .and measurable_const ?_
  exact test1

lemma measurable_finsetSum₂ {M ι : Type*} [AddCommMonoid M] [MeasurableSpace M] [MeasurableAdd₂ M] :
    Measurable fun (sf : Finset ι × (ι → M)) ↦ ∑ i ∈ sf.1, sf.2 i := by
  sorry

end LinearOrder

variable [ConditionallyCompleteLinearOrderBot ι] {𝓕 : Filtration ι mΩ}

private def aux_time (ε : ℝ) : ℕ → Ω → WithTop ι
  | 0 => ⊤
  | n + 1 => fun ω ↦ sInf {t : WithTop ι | ∃ (h : t ≠ ⊤) ∧ ε ≤ ‖X (aux_time ε n ω) ω - X s ω‖ ∧
      1 / 2 ^ k ≤ ‖X (T k n) ω - X s ω + Δ (X · ω) s‖}

lemma isThinSet_jumpSet [TopologicalSpace ι] [OrderTopology ι]
    [SecondCountableTopology ι] (hX1 : StronglyAdapted 𝓕 X) (hX2 : ∀ ω, IsCadlag (X · ω)) :
    IsThinSet {(t, ω) | ⊥ < t ∧ Δ (X · ω) t ≠ 0} 𝓕 := by
  let T (k : ℕ) : ℕ → Ω → WithTop ι :=
    | 0 => ⊥
    | n + 1 => fun ω ↦ sInf {t | ∃ s : ι, t = s ∧ 1 / 2 ^ k ≤ ‖X (T k n) ω - X s ω‖ ∧
        1 / 2 ^ k ≤ ‖X (T k n) ω - X s ω + Δ (X · ω) s‖}

nonrec lemma IsCadlag.largeJumpProcess [TopologicalSpace ι] {ω : Ω} (hX : IsCadlag (X · ω)) :
    IsCadlag (largeJumpProcess X ε · ω) := by
  constructor
  · intro s

nonrec lemma StronglyAdapted.largeJumpProcess [SecondCountableTopology E]
    [TopologicalSpace ι] [FirstCountableTopology ι] [OrderTopology ι]
    (hX1 : StronglyAdapted 𝓕 X) (hX2 : ∀ ω, IsCadlag (X · ω)) :
    StronglyAdapted 𝓕 (largeJumpProcess X ε) := by
  intro t
  rw [largeJumpProcess_def]
  borelize E
  rw [stronglyMeasurable_iff_measurable]
  convert measurable_finsetSum₂.comp
    (f := fun ω ↦ (largeJumpFinsetLe (⟨(X · ω), hX2 ω⟩ : {f : ι → E // IsCadlag f}).1 ε t, (X · ω))) ?_
  · simp

variable [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]

lemma variationProcess_largeJumpProcess (X : ι → Ω → E) (ε : ℝ) (t : ι) (ω : Ω) :
    variationProcess (largeJumpProcess X ε) ⊥ t ω =
      ∑' s : largeJumpFinsetLe (X · ω) ε t, ‖Δ (X · ω) s‖ := by
  rw [variationProcess]

lemma IsLocalMartingale.locally_integrable_largeJumpProcess (hX : IsLocalMartingale X 𝓕 P)
    {ε : ℝ} (hε : 0 < ε) :
    Locally (fun X ↦ StronglyAdapted 𝓕 X ∧ (∀ ω, LocallyBoundedVariationOn (X · ω) Set.univ) ∧
      Integrable (𝓕.limitProcess (variationProcess X ⊥) P) P) 𝓕 (largeJumpProcess X ε) P := by
  borelize ι
  rw [IsStable.locally_and_iff, IsStable.locally_and_iff]
  · refine ⟨?_, .of_prop fun ω ↦ ?_, ?_⟩
    ·
  -- obtain ⟨τ, hτ1, hτ2⟩ := hX
