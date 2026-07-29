/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import BrownianMotion.StochasticIntegral.StochasticInterval

@[expose] public section

open ProbabilityTheory ENNReal

namespace MeasureTheory

variable {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
  {τ : Ω → WithTop ι} {A : Set Ω}

section Preorder

variable [Preorder ι] {𝓕 : Filtration ι mΩ}

lemma isStoppingTime_piecewise [DecidablePred (· ∈ A)]
    (hτ : IsStoppingTime 𝓕 τ) (hA : MeasurableSet[hτ.measurableSpace] A) :
    IsStoppingTime 𝓕 (A.piecewise τ (fun _ ↦ ⊤)) := by
  intro t
  convert ((hτ.measurableSet A).1 hA).2 t
  ext ω
  simp only [Set.piecewise, Set.mem_ofPred_eq, Set.mem_inter_iff]
  split_ifs <;> simp_all

variable [OrderBot ι]

@[instance_reducible]
def leftMeasurableSpace (𝓕 : Filtration ι mΩ) (τ : Ω → WithTop ι) : MeasurableSpace Ω :=
  𝓕 ⊥ ⊔ (MeasurableSpace.generateFrom {s | ∃ A t, MeasurableSet[𝓕 t] A ∧ s = A ∩ {ω | t < τ ω}})

def IsPredictableTime (𝓕 : Filtration ι mΩ) (τ : Ω → WithTop ι) : Prop :=
  MeasurableSet[𝓕.predictable] (stochIco τ (fun _ ↦ ⊤))

lemma IsPredictableTime.isStoppingTime (hτ : IsPredictableTime 𝓕 τ) :
    IsStoppingTime 𝓕 τ := by
  intro t
  have : {ω | τ ω ≤ t} = (Prod.mk t) ⁻¹' (stochIco τ (fun _ ↦ ⊤)) := by ext; simp
  rw [this]
  convert hτ.preimage (measurable_generateFrom (fun A hA ↦ ?_))
  simp only [Set.mem_union, Set.mem_ofPred_eq] at hA
  classical
  obtain ⟨A, hA, rfl⟩ | ⟨s, A, hA, rfl⟩ := hA <;> rw [Set.mk_preimage_prod_right_eq_if]
  · split_ifs
    · grind
    · convert MeasurableSet.empty
  · split_ifs with h
    · exact (𝓕.mono h.le) A hA
    · convert MeasurableSet.empty

structure IsAccessibleTime (𝓕 : Filtration ι mΩ) (τ : Ω → WithTop ι) : Prop where
  isStoppingTime : IsStoppingTime 𝓕 τ
  stochIco_subset : ∃ σ : ℕ → Ω → WithTop ι,
    (∀ n, IsPredictableTime 𝓕 (σ n)) ∧ stochGraph τ ⊆ ⋃ n, stochGraph (σ n)

structure IsInacessibleTime (𝓕 : Filtration ι mΩ) (τ : Ω → WithTop ι) (P : Measure Ω) : Prop where
  isStoppingTime : IsStoppingTime 𝓕 τ
  measure_eq_lt_top_eq_zero : ∀ σ, IsPredictableTime 𝓕 σ → P {ω | τ ω = σ ω ∧ σ ω < ⊤} = 0

end Preorder

variable [LinearOrder ι] [OrderBot ι] {𝓕 : Filtration ι mΩ}

theorem Set.iInter_prod {α β ι : Type*} {s : Set α} {t : ι → Set β} [hι : Nonempty ι] :
    (⋂ (i : ι), t i) ×ˢ s = ⋂ (i : ι), t i ×ˢ s := sorry

lemma IsPredictableTime.const [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]
    (𝓕 : Filtration ι mΩ) (t : WithTop ι) :
    IsPredictableTime 𝓕 (fun _ ↦ t) := by
  rw [IsPredictableTime]
  cases t with
  | top =>
    convert MeasurableSet.empty
    ext; simp [stochIco]
  | coe t =>
    have : (stochIco (fun _ ↦ (t : WithTop ι)) (fun _ ↦ ⊤) : Set (ι × Ω)) =
      (Set.Ici t) ×ˢ Set.univ := by ext; simp [stochIco]
    rw [this]
    by_cases h : Order.IsSuccLimit t
    · obtain ⟨u, mu, hu1, hu2, -⟩ := h.isLUB_Iio.exists_seq_strictMono_tendsto_of_notMem (by simp)
        h.nonempty_Iio
      have : Set.Ici t = ⋂ n, Set.Ioi (u n) := by
        ext s
        simp only [Set.mem_Ici, Set.mem_iInter, Set.mem_Ioi]
        exact ⟨fun h n ↦ (hu1 n).trans_le h, fun h ↦ le_of_tendsto' hu2 (fun n ↦ (h n).le)⟩
      rw [this, Set.iInter_prod]
      exact .iInter (fun _ ↦ measurableSet_predictable_Ioi_prod .univ)
    rw [Order.isSuccLimit_iff, Order.IsSuccPrelimit] at h
    push +distrib Not at h
    obtain h | h := h
    · convert MeasurableSet.univ
      grind [IsMin]
    · obtain ⟨s, hs⟩ := h
      convert measurableSet_predictable_Ioi_prod (i := s) .univ
      grind [CovBy]

variable {mΩ} {P : Measure Ω}

/-- Any stopping time can be decomposed into an accessible time and a totally inaccessible time. -/
theorem target [∀ ω (s : Set Ω), Decidable (ω ∈ s)] [TopologicalSpace ι] [OrderTopology ι]
    [SecondCountableTopology ι] [IsFiniteMeasure P] (hτ : IsStoppingTime 𝓕 τ) :
    ∃ A, MeasurableSet[leftMeasurableSpace 𝓕 τ] A ∧ A ⊆ {ω | τ ω < ⊤} ∧
      IsAccessibleTime 𝓕 (A.piecewise τ (fun _ ↦ ⊤)) ∧
      IsInacessibleTime 𝓕 (Aᶜ.piecewise τ (fun _ ↦ ⊤)) P := by
  classical
  let S := {x : ℝ≥0∞ | ∃ σ : ℕ → Ω → WithTop ι, (∀ n, IsPredictableTime 𝓕 (σ n)) ∧
    x = P (⋃ n, {ω | τ ω = σ n ω ∧ σ n ω < ⊤})}
  have hS1 : S.Nonempty := ⟨_, ⟨fun _ _ ↦ ⊥, fun _ ↦ .const 𝓕 ⊥, rfl⟩⟩
  have hS2 : BddAbove S := ⟨P Set.univ, by
    rintro - ⟨_, _, rfl⟩
    exact measure_mono (by simp)⟩
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_seq_tendsto_sSup hS1 hS2
  simp only [Set.mem_ofPred_eq, S] at hu3
  choose σ hσ1 hσ2 using hu3
  refine ⟨⋃ n, ⋃ k, {ω | τ ω = σ n k ω ∧ σ n k ω < ⊤}, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · refine .iUnion fun n ↦ .iUnion fun k ↦ ?_
    sorry
  · simp +contextual
  · refine isStoppingTime_piecewise hτ (.iUnion fun n ↦ .iUnion fun k ↦ ?_)
    have : {ω | τ ω = σ n k ω ∧ σ n k ω < ⊤} = {ω | τ ω = σ n k ω ∧ τ ω < ⊤} := by grind
    rw [this, Set.ofPred_and]
    refine (hτ.measurableSet_eq_stopping_time (hσ1 n k).isStoppingTime).inter ?_
    refine (hτ.measurableSet _).2 ⟨?_, ?_⟩
    · convert hτ.measurableSet_eq_top'.compl
      ext ω
      exact ⟨fun h ↦ h.ne, fun (h : τ ω ≠ ⊤) ↦ h.lt_top⟩
    · convert fun t ↦ hτ t
      ext
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_iff_right_iff_imp]
      intro h
      exact h.trans_lt (by simp)
  · obtain ⟨φ, hφ⟩ := exists_surjective_nat (ℕ × ℕ)
    refine ⟨fun n ↦ σ (φ n).1 (φ n).2, fun n ↦ hσ1 _ _, fun tω h ↦ ?_⟩
    simp only [stochGraph, Set.piecewise, Set.mem_iUnion, Set.mem_ofPred_eq] at h ⊢
    split_ifs at h with h'
    · obtain ⟨n, k, h1, h2⟩ := h'
      obtain ⟨i, hi⟩ := hφ (n, k)
      use i
      simp_all
    · contradiction
  · refine isStoppingTime_piecewise hτ (.compl (.iUnion fun n ↦ .iUnion fun k ↦ ?_))
    have : {ω | τ ω = σ n k ω ∧ σ n k ω < ⊤} = {ω | τ ω = σ n k ω ∧ τ ω < ⊤} := by grind
    rw [this, Set.ofPred_and]
    refine (hτ.measurableSet_eq_stopping_time (hσ1 n k).isStoppingTime).inter ?_
    refine (hτ.measurableSet _).2 ⟨?_, ?_⟩
    · convert hτ.measurableSet_eq_top'.compl
      ext ω
      exact ⟨fun h ↦ h.ne, fun (h : τ ω ≠ ⊤) ↦ h.lt_top⟩
    · convert fun t ↦ hτ t
      ext
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_iff_right_iff_imp]
      intro h
      exact h.trans_lt (by simp)
  · intro π hπ
    have : {ω | (⋃ n, ⋃ k, {ω | τ ω = σ n k ω ∧ σ n k ω < ⊤})ᶜ.piecewise τ (fun x ↦ ⊤) ω = π ω ∧
      π ω < ⊤} = ((⋃ n, ⋃ k, {ω | τ ω = σ n k ω ∧ σ n k ω < ⊤})ᶜ ∩
          {ω | τ ω = π ω ∧ π ω < ⊤}) := by
      ext ω
      simp only [Set.piecewise, Set.compl_iUnion, Set.mem_iInter, Set.mem_compl_iff,
        Set.mem_ofPred_eq, not_and, not_lt, top_le_iff, Set.mem_inter_iff]
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · split_ifs at h with h'
        · exact ⟨fun k n h'' ↦ h' _ _ h'', h.1, h.2⟩
        · grind
      · split_ifs with h'
        · exact ⟨h.2.1, h.2.2⟩
        · grind
    rw [this]
    by_contra!
    have key n : u n + P ((⋃ m, ⋃ k, {ω | τ ω = σ m k ω ∧ σ m k ω < ⊤})ᶜ ∩
          {ω | τ ω = π ω ∧ π ω < ⊤}) ≤ sSup S := by
      refine le_trans (b := u n + P ((⋃ k, {ω | τ ω = σ n k ω ∧ σ n k ω < ⊤})ᶜ ∩
          {ω | τ ω = π ω ∧ π ω < ⊤})) ?_ ?_
      · gcongr 4 with
        exact Set.subset_iUnion (fun m ↦ ⋃ k, {ω | τ ω = σ m k ω ∧ σ m k ω < ⊤}) n
      refine le_sSup_of_le (b := P ((⋃ k, {ω | τ ω = σ n k ω ∧ σ n k ω < ⊤}) ∪
        {ω | τ ω = π ω ∧ π ω < ⊤})) ?_ ?_
      · obtain ⟨φ, hφ⟩ := exists_surjective_nat (ℕ ⊕ Unit)
        refine ⟨fun k ↦ Sum.elim (σ n) (fun _ ↦ π) (φ k), fun k ↦ ?_, ?_⟩
        · simp only
          cases φ k with
          | inl l => exact hσ1 n l
          | inr _ => exact hπ
        · congr with ω
          simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq]
          constructor
          · rintro (⟨i, hi1, hi2⟩ | ⟨h1, h2⟩)
            · obtain ⟨j, hj⟩ := hφ (.inl i)
              use j
              simp_all
            · obtain ⟨j, hj⟩ := hφ (.inr ())
              use j
              simp_all
          · rintro ⟨i, hi1, hi2⟩
            cases hi : φ i with
            | inl j =>
              left
              use j
              simp_all
            | inr _ =>
              right
              simp_all
      · grw [hσ2, ← measure_union, measure_mono]
        · grind
        · grind
        refine .inter (.compl (.iUnion fun k ↦ ?_)) ?_
        · rw [Set.ofPred_and]
          refine (hτ.measurableSpace_le _
              (hτ.measurableSet_eq_stopping_time (hσ1 n k).isStoppingTime)).inter ?_
          exact measurableSet_Iio.preimage (hσ1 n k).isStoppingTime.measurable'
        · rw [Set.ofPred_and]
          refine (hτ.measurableSpace_le _
              (hτ.measurableSet_eq_stopping_time hπ.isStoppingTime)).inter ?_
          exact measurableSet_Iio.preimage hπ.isStoppingTime.measurable'
    have final := le_of_tendsto' (hu2.add_const _) key
    suffices sSup S < sSup S by grind
    calc
    sSup S
      < sSup S +
        P ((⋃ n, ⋃ k, {ω | τ ω = σ n k ω ∧ σ n k ω < ⊤})ᶜ ∩ {ω | τ ω = π ω ∧ π ω < ⊤}) := by
        grw [← pos_of_ne_zero this, add_zero]
        apply ne_top_of_le_ne_top (b := P Set.univ)
        · simp
        · rw [sSup_le_iff]
          rintro - ⟨_, _, rfl⟩
          exact measure_mono (by simp)
    _ ≤ sSup S := final

end MeasureTheory
