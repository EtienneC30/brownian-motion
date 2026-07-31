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
  [NormedSpace ℝ E] {P : Measure Ω} {X : ι → Ω → E} {ε : ℝ} {s t : ι} {n : ℕ}

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

private noncomputable def auxTime (X : ι → Ω → E) (ε : ℝ) : ℕ → Ω → WithTop ι
  | 0 => ⊤
  | n + 1 => fun ω ↦ if auxTime X ε n ω = ⊤ then ⊤ else
      sInf {t : WithTop ι | (t ≠ ⊤) ∧ ε ≤ ‖X (auxTime X ε n ω).untopA ω - X t.untopA ω‖ ∧
      ε ≤ ‖X (auxTime X ε n ω).untopA ω - X t.untopA ω + Δ (X · ω) t.untopA‖}

private lemma isStoppingTime_auxTime : IsStoppingTime 𝓕 (auxTime X ε n) := by sorry

lemma isThinSet_jumpSet [TopologicalSpace ι] [OrderTopology ι]
    [SecondCountableTopology ι] (hX1 : StronglyAdapted 𝓕 X) (hX2 : ∀ ω, IsCadlag (X · ω)) :
    IsThinSet {(t, ω) | ⊥ < t ∧ Δ (X · ω) t ≠ 0} 𝓕 := by
  let T (k : ℕ) n ω : WithTop ι := auxTime X (1 / 2 ^ k) n ω
  have hT k n : IsStoppingTime 𝓕 (T k n) := isStoppingTime_auxTime
  obtain ⟨φ, hφ⟩ := exists_surjective_nat (ℕ × ℕ)
  borelize ι
  refine .mono ⟨fun n ↦ T (φ n).1 (φ n).2, fun n ↦ hT (φ n).1 (φ n).2, rfl⟩ ?_ ?_
  · intro (t, ω) htω
    simp only [ne_eq, Set.mem_ofPred_eq] at htω
    have := norm_pos_iff.2 htω.2
    obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 / 2 ^ k ≤ ‖Δ (X · ω) t‖ := by
      refine Eventually.exists (f := atTop) (Filter.Tendsto.eventually ?_ (eventually_le_nhds this))
      apply Tendsto.const_div_atTop
      convert tendsto_natCast_atTop_atTop.comp <| tendsto_rpow_atTop (by simp)
      sorry

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
