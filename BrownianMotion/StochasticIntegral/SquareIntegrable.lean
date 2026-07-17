/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Auxiliary.Martingale
public import BrownianMotion.StochasticIntegral.LocalMartingale
public import Mathlib.Probability.Notation

/-! # Square integrable martingales

-/

@[expose] public section

open MeasureTheory Filter Function TopologicalSpace
open scoped ENNReal Topology RealInnerProductSpace

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι] [TopologicalSpace ι]
  [NormedAddCommGroup E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ι → Ω → E} {𝓕 : Filtration ι mΩ}

section NormedSpace

variable [NormedSpace ℝ E]

/-- A square integrable martingale is a martingale with cadlag paths and uniformly bounded
second moments. -/
structure IsSquareIntegrable (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) : Prop where
  martingale : Martingale X 𝓕 P
  cadlag : ∀ᵐ ω ∂P, IsCadlag (X · ω)
  bounded : ⨆ i, eLpNorm (X i) 2 P < ∞

def IsAESquareIntegrable (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) : Prop :=
  ∃ Y : ι → Ω → E, IsSquareIntegrable Y 𝓕 P ∧ ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω

lemma IsAESquareIntegrable.congr {X Y : ι → Ω → E} (hX : IsAESquareIntegrable X 𝓕 P)
    (hXY : ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω) : IsAESquareIntegrable Y 𝓕 P := by
  obtain ⟨Z, hZ1, hZ2⟩ := hX
  refine ⟨Z, hZ1, ?_⟩
  filter_upwards [hZ2, hXY] with ω h1 h2
  grind

lemma isAESquareIntegrable_congr {X Y : ι → Ω → E} (hXY : ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω) :
    IsAESquareIntegrable X 𝓕 P ↔ IsAESquareIntegrable Y 𝓕 P where
  mp h := h.congr hXY
  mpr h := by
    refine h.congr ?_
    filter_upwards [hXY]
    grind

lemma IsSquareIntegrable.const_fun [OrderBot ι] {ξ : Ω → E} (mξ : StronglyMeasurable[𝓕 ⊥] ξ)
    [SigmaFiniteFiltration P 𝓕] (hξ1 : Integrable ξ P) (hξ2 : MemLp ξ 2 P) :
    IsSquareIntegrable (fun _ ↦ ξ) 𝓕 P where
  martingale := martingale_const_fun 𝓕 P mξ hξ1
  cadlag := ae_of_all _ fun _ ↦ isCadlag_const _
  bounded := by
    rw [iSup_const]
    exact hξ2.2

/-- A stochastic process is locally square-integrable if it satisfies the square-integrable
martingale property locally. -/
def IsLocallySquareIntegrable [OrderBot ι] [OrderTopology ι]
    (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω := by volume_tac) : Prop :=
  Locally (fun Y ↦ IsSquareIntegrable Y 𝓕 P) 𝓕 X P

lemma IsSquareIntegrable.isLocallySquareIntegrable [OrderBot ι] [OrderTopology ι]
    (hX : IsSquareIntegrable X 𝓕 P) :
    IsLocallySquareIntegrable X 𝓕 P :=
  Locally.of_prop hX

lemma IsSquareIntegrable.integrable_sq (hX : IsSquareIntegrable X 𝓕 P) (i : ι) :
    Integrable (fun ω ↦ ‖X i ω‖ ^ 2) P := by
  constructor
  · have hX_meas := (hX.martingale.stronglyAdapted i).mono (𝓕.le i)
    fun_prop
  · have hX_bound : eLpNorm (X i) 2 P < ∞ := by
      calc eLpNorm (X i) 2 P
      _ ≤ ⨆ j, eLpNorm (X j) 2 P := le_iSup (fun j ↦ eLpNorm (X j) 2 P) i
      _ < ∞ := hX.bounded
    simpa [HasFiniteIntegral, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top] using hX_bound

@[to_fun]
lemma IsSquareIntegrable.add [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P)
    (hY : IsSquareIntegrable Y 𝓕 P) :
    IsSquareIntegrable (X + Y) 𝓕 P := by
  refine ⟨hX.martingale.add hY.martingale, ?_, ?_⟩
  · filter_upwards [hX.cadlag, hY.cadlag] with ω hX hY using hX.add hY
  have hX_bound : ⨆ i, eLpNorm (X i) 2 P < ∞ := hX.bounded
  have hY_bound : ⨆ i, eLpNorm (Y i) 2 P < ∞ := hY.bounded
  calc ⨆ i, eLpNorm (fun ω ↦ X i ω + Y i ω) 2 P
      ≤ ⨆ i, (eLpNorm (X i) 2 P + eLpNorm (Y i) 2 P) := by
        refine iSup_mono fun i ↦ ?_
        exact eLpNorm_add_le
          ((hX.martingale.stronglyAdapted i).mono (𝓕.le i)).aestronglyMeasurable
          ((hY.martingale.stronglyAdapted i).mono (𝓕.le i)).aestronglyMeasurable (by simp)
    _ ≤ (⨆ i, eLpNorm (X i) 2 P) + ⨆ i, eLpNorm (Y i) 2 P := by
        refine iSup_le fun i => ?_
        gcongr
        · exact le_iSup (fun i => eLpNorm (X i) 2 P) i
        · exact le_iSup (fun i => eLpNorm (Y i) 2 P) i
    _ < ∞ := ENNReal.add_lt_top.mpr ⟨hX_bound, hY_bound⟩

@[to_fun]
lemma IsSquareIntegrable.smul [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P) (r : ℝ) :
    IsSquareIntegrable (r • X) 𝓕 P where
  martingale := hX.martingale.smul r
  cadlag := by
    filter_upwards [hX.cadlag] with ω h using h.const_smul r
  bounded := by
    change (⨆ i, eLpNorm (r • X i) 2 P) < ∞
    simp only [eLpNorm_const_smul, ← ENNReal.mul_iSup]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hX.bounded

@[to_fun]
lemma IsSquareIntegrable.neg [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P) :
    IsSquareIntegrable (-X) 𝓕 P := by
  simpa using hX.smul (-1)

@[to_fun]
lemma IsSquareIntegrable.sub [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P)
    (hY : IsSquareIntegrable Y 𝓕 P) :
    IsSquareIntegrable (X - Y) 𝓕 P := by
  simpa [sub_eq_add_neg] using (hX.add hY.neg)

lemma IsSquareIntegrable.sub_bot [SigmaFiniteFiltration P 𝓕] [CompleteSpace E] [OrderBot ι]
    {X : ι → Ω → E}
    (hX : IsSquareIntegrable X 𝓕 P) :
    IsSquareIntegrable (X · - X ⊥) 𝓕 P := by
  apply hX.sub
  apply IsSquareIntegrable.const_fun
  · exact hX.martingale.stronglyMeasurable ⊥
  · exact hX.martingale.integrable ⊥
  · exact ⟨(hX.martingale.stronglyMeasurable ⊥).mono (𝓕.le' ⊥) |>.aestronglyMeasurable,
      (le_iSup (fun i ↦ eLpNorm (X i) 2 P) ⊥).trans_lt hX.bounded⟩

variable [SigmaFiniteFiltration P 𝓕]

lemma IsSquareIntegrable.submartingale_sq_norm [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P) :
    Submartingale (fun i ω ↦ ‖X i ω‖ ^ 2) 𝓕 P := by
  refine hX.1.submartingale_convex_comp (φ := fun x ↦ ‖x‖ ^ 2) ?_ (by fun_prop) fun i ↦ ?_
  · exact ConvexOn.pow convexOn_univ_norm (fun _ _ ↦ by positivity) 2
  · refine MemLp.integrable_norm_pow ⟨?_, ?_⟩ (by linarith)
    · exact hX.1.1.stronglyMeasurable.aestronglyMeasurable
    · exact lt_of_le_of_lt (le_iSup (fun i ↦ eLpNorm (X i) 2 P) i) hX.3

/-- A locally square-integrable martingale has locally submartingale squared norm. -/
lemma IsLocallySquareIntegrable.isLocalSubmartingale_sq_norm
    [OrderBot ι] [OrderTopology ι] [CompleteSpace E]
    (hX : IsLocallySquareIntegrable X 𝓕 P) :
    IsLocalSubmartingale (fun t ω ↦ ‖X t ω‖ ^ 2) 𝓕 P := by
  have h_stopped_sq_norm {τ : Ω → WithTop ι} :
      stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (fun ω ↦ ‖X t ω‖ ^ 2)) τ =
        fun t ω ↦ ‖stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (X t)) τ t ω‖ ^ 2 := by
    ext t ω
    by_cases hτ : ⊥ < τ ω <;> simp [stoppedProcess, hτ]
  unfold IsLocalSubmartingale
  change Locally (fun Y : ι → Ω → ℝ ↦ Submartingale Y 𝓕 P ∧
      ∀ᵐ ω ∂P, IsCadlag (Y · ω)) 𝓕 (fun t ω ↦ ‖X t ω‖ ^ 2) P
  refine ⟨hX.localSeq, hX.isLocalizingSequence_localSeq, fun n ↦ ?_⟩
  have hXn := hX.stoppedProcess_localSeq n
  constructor
  · simpa [h_stopped_sq_norm] using hXn.submartingale_sq_norm
  · filter_upwards [hXn.cadlag] with ω hXn
    simpa [h_stopped_sq_norm] using hXn.norm_sq

lemma IsSquareIntegrable.eLpNorm_mono [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P)
    {i j : ι} (hij : i ≤ j) :
    eLpNorm (X i) 2 P ≤ eLpNorm (X j) 2 P := by
  have : ∫ ω, ‖X i ω‖ ^ 2 ∂P ≤ ∫ ω, ‖X j ω‖ ^ 2 ∂P := by
    simpa using hX.submartingale_sq_norm.setIntegral_le hij MeasurableSet.univ
  calc
  _ = (∫⁻ ω, ‖X i ω‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂P) ^ (1 / (2 : ℝ≥0∞).toReal) := by
    simp [eLpNorm_eq_lintegral_rpow_enorm_toReal]
  _ = (ENNReal.ofReal (∫ ω, ‖X i ω‖ ^ 2 ∂P)) ^ (1 / (2 : ℝ≥0∞).toReal) := by
    congr
    simpa using (ofReal_integral_norm_eq_lintegral_enorm (hX.integrable_sq i)).symm
  _ ≤ (ENNReal.ofReal (∫ ω, ‖X j ω‖ ^ 2 ∂P)) ^ (1 / (2 : ℝ≥0∞).toReal) := by gcongr
  _ = (∫⁻ ω, ‖X j ω‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂P) ^ (1 / (2 : ℝ≥0∞).toReal) := by
    congr
    simpa using (ofReal_integral_norm_eq_lintegral_enorm (hX.integrable_sq j))
  _ = eLpNorm (X j) 2 P := by
    simp [eLpNorm_eq_lintegral_rpow_enorm_toReal]

lemma IsSquareIntegrable.ae_tendsto_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (𝓕.limitProcess X P ω)) := by
  sorry

lemma IsSquareIntegrable.tendsto_eLpNorm_two_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    Tendsto (fun i ↦ eLpNorm (X i - 𝓕.limitProcess X P) 2 P) atTop (𝓝 0) := by
  sorry

lemma IsSquareIntegrable.iSup_eLpNorm_eq_eLpNorm_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    ⨆ i, eLpNorm (X i) 2 P = eLpNorm (𝓕.limitProcess X P) 2 P := by
  sorry

end NormedSpace

section Hilbert

variable [InnerProductSpace ℝ E] [CompleteSpace E] [SigmaFiniteFiltration P 𝓕]


variable (ι E P 𝓕) in
/-- The type of square integrable martingales. -/
def SquareIntegrable : Submodule ℝ (Ω →ₘ[P] (ι → E)) where
  carrier := {X | ∃ Y : ι → Ω → E, IsSquareIntegrable Y 𝓕 P ∧ (fun ω t ↦ Y t ω) =ᵐ[P] X}
  add_mem' {X Y} hX hY := by
    obtain ⟨Z, hZ1, hZ2⟩ := hX
    obtain ⟨T, hT1, hT2⟩ := hY
    refine ⟨Z + T, hZ1.add hT1, ?_⟩
    filter_upwards [hZ2, hT2, X.coeFn_add Y] with ω h1 h2 h3
    rw [funext_iff] at h1 h2 ⊢
    simp_all
  zero_mem' := by
    refine ⟨0, sorry, AEEqFun.coeFn_zero.symm⟩
  smul_mem' c {X} hX := by
    obtain ⟨Y, hY1, hY2⟩ := hX
    refine ⟨c • Y, hY1.smul c, ?_⟩
    filter_upwards [hY2, X.coeFn_smul c] with ω h1 h2
    rw [funext_iff] at h1 ⊢
    simp_all

noncomputable def SquareIntegrable.out (X : SquareIntegrable ι E P 𝓕) : ι → Ω → E := X.2.choose

lemma SquareIntegrable.isSquareIntegrable_out (X : SquareIntegrable ι E P 𝓕) :
    IsSquareIntegrable (SquareIntegrable.out X) 𝓕 P := X.2.choose_spec.1

lemma SquareIntegrable.ae_eq_out (X : SquareIntegrable ι E P 𝓕) :
    ∀ᵐ ω ∂P, ∀ t, X.1 ω t = SquareIntegrable.out X t ω := by
  filter_upwards [X.2.choose_spec.2] with ω h t
  rw [← h]
  rfl

noncomputable def SquareIntegrable.mk (X : ι → Ω → E) (hX : IsAESquareIntegrable X 𝓕 P) :
    SquareIntegrable ι E P 𝓕 :=
  ⟨.mk (fun ω t ↦ X t ω) sorry, ⟨hX.choose, hX.choose_spec.1,
    by {
      grw [AEEqFun.coeFn_mk]
      filter_upwards [hX.choose_spec.2] with ω h1
      simp [h1]
    }⟩⟩

lemma SquareIntegrable.mk_eq_mk {X Y : ι → Ω → E} {hX : IsAESquareIntegrable X 𝓕 P}
    {hY : IsAESquareIntegrable Y 𝓕 P} :
    SquareIntegrable.mk X hX = SquareIntegrable.mk Y hY ↔ ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω where
  mp h := by
    rw [Subtype.ext_iff] at h
    simp only [mk] at h
    filter_upwards [AEEqFun.mk_eq_mk.1 h] with ω h1
    rwa [← funext_iff]
  mpr h := by
    ext : 1
    simp only [mk]
    rw [AEEqFun.mk_eq_mk]
    filter_upwards [h] with ω h
    rwa [funext_iff]

-- instance : S (SquareIntegrable ι E P 𝓕) := sorry

lemma IsSquareIntegrable.tendsto_ae_limitProcess
    {X : ι → Ω → E} (hX : IsSquareIntegrable X 𝓕 P) :
    ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (𝓕.limitProcess X P ω)) := sorry

instance [Nonempty ι] : NormedAddCommGroup (SquareIntegrable ι E P 𝓕) where
  norm X := √(P[fun ω ↦ ‖𝓕.limitProcess (SquareIntegrable.out X) P ω‖^2])
  dist_self X := by
    simp only [neg_add_cancel]
    rw [Real.sqrt_eq_zero (by positivity), integral_eq_zero_iff_of_nonneg_ae]
    · have : ∀ᵐ ω ∂P, 𝓕.limitProcess (SquareIntegrable.out (0 : SquareIntegrable ι E P 𝓕)) P ω =
          0 := by
        filter_upwards [(SquareIntegrable.isSquareIntegrable_out
          (0 : SquareIntegrable ι E P 𝓕)).tendsto_ae_limitProcess,
          (SquareIntegrable.ae_eq_out (0 : SquareIntegrable ι E P 𝓕)),
          AEEqFun.coeFn_zero (α := Ω) (β := ι → E)] with ω h1 h2 h3
        simp only [ZeroMemClass.coe_zero] at h2
        apply tendsto_nhds_unique h1
        simp_rw [← h2, h3]
        simp
      filter_upwards [this] with ω h
      rw [h]
      simp
    · exact ae_of_all _ fun _ ↦ by positivity

  dist_comm := sorry
  dist_triangle := sorry
  eq_of_dist_eq_zero := sorry

instance : InnerProductSpace ℝ (SquareIntegrable ι E P 𝓕) where
  -- smul c X := ⟨c • X.1, by {
  --   obtain ⟨Y, hY1, hY2⟩ := X.2
  --   refine ⟨c • Y, hY1.smul c, ?_⟩
  --   filter_upwards [hY2, AEEqFun.coeFn_smul c X.1] with ω h1 h2
  --   rw [h2]
  --   rw [funext_iff] at h1
  --   ext t
  --   simp [h1]
  -- }⟩
  -- mul_smul a b X := by
  --   change (⟨(a * b) • X.1, _⟩ : SquareIntegrable ι E P 𝓕) = ⟨a • _, _⟩
  --   congr 1
  --   rw [mul_smul]
  --   congr
  -- one_smul X := by
  --   change (⟨1 • X.1, _⟩ : SquareIntegrable ι E P 𝓕) = _
  --   congr
  --   simp
  -- smul_zero X :=

lemma SquareIntegrable.inner_eq {X Y : SquareIntegrable ι E P 𝓕} :
    ⟪X, Y⟫ = P[fun ω ↦ ⟪𝓕.limitProcess (fun t ω ↦ X.1 ω t) P ω,
      𝓕.limitProcess (fun t ω ↦ Y.1 ω t) P ω⟫] := sorry

lemma SquareIntegrable.coe_add (X Y : SquareIntegrable ι E P 𝓕) :
    (X + Y).1 = X.1 + Y.1 := by
  sorry

@[simp]
lemma SquareIntegrable.coe_zero : (0 : SquareIntegrable ι E P 𝓕).1 = 0 := by
  sorry

lemma SquareIntegrable.coe_smul (X : SquareIntegrable ι E P 𝓕) (c : ℝ) :
    (c • X).1 = c • X.1 := by
  sorry

instance : CompleteSpace (SquareIntegrable ι E P 𝓕) := by
  sorry

variable [CompleteSpace E]

variable (ι E P 𝓕) in
/-- The set of continuous square integrable martingales, as a submodule of the type of
square-integrable martingales, see `SquareIntegrable`. -/
def continuousSquareIntegrable : Submodule ℝ (SquareIntegrable ι E P 𝓕) where
  carrier := {X | ∃ Y : ι → Ω → E, (∀ ω, Continuous (Y · ω)) ∧ IsSquareIntegrable Y 𝓕 P ∧
      (fun ω t ↦ Y t ω) =ᵐ[P] X.1}
  add_mem' := by
    rintro X Y ⟨X', hX1, hX2, hX3⟩ ⟨Y', hY1, hY2, hY3⟩
    refine ⟨X' + Y', fun ω ↦ (hX1 ω).add (hY1 ω), hX2.add hY2, ?_⟩
    grw [SquareIntegrable.coe_add, AEEqFun.coeFn_add, ← hX3, ← hY3]
    rfl
  zero_mem' := by
    refine ⟨0, by fun_prop, sorry, ?_⟩
    grw [SquareIntegrable.coe_zero, AEEqFun.coeFn_zero]
    rfl
  smul_mem' := by
    rintro c X ⟨X', hX1, hX2, hX3⟩
    refine ⟨c • X', fun ω ↦ (hX1 ω).const_smul c, hX2.smul c, ?_⟩
    grw [SquareIntegrable.coe_smul, AEEqFun.coeFn_smul, ← hX3]
    rfl

noncomputable def continuousSquareIntegrable.out (X : continuousSquareIntegrable ι E P 𝓕) :
    ι → Ω → E :=
  X.2.choose

lemma continuous_out (X : continuousSquareIntegrable ι E P 𝓕) (ω : Ω) :
    Continuous (continuousSquareIntegrable.out X · ω) :=
  X.2.choose_spec.1 ω

lemma isSquareIntegrable_out (X : continuousSquareIntegrable ι E P 𝓕) :
    IsSquareIntegrable (continuousSquareIntegrable.out X) 𝓕 P :=
  X.2.choose_spec.2.1

lemma out_ae_eq (X : continuousSquareIntegrable ι E P 𝓕) :
    (fun ω t ↦ continuousSquareIntegrable.out X t ω) =ᵐ[P] X.1.1 :=
  X.2.choose_spec.2.2

instance : IsClosed (continuousSquareIntegrable ι E P 𝓕 : Set (SquareIntegrable ι E P 𝓕)) := by
  sorry

open scoped Classical in
/-- The continuous martingale part of a square-integrable martingale `X`. This is defined as the
projection of `X` onto the closed subspace of continuous square-integrable martingales.

TODO: we rely on the already existing `AEEqFun` machinery, but this is about equivalence classes
of strongly measurable functions, while here we are interested in undistinguishability only
so measurablility is the way to go. It seems we will need to duplicate `AEEqFun` for the measurable
case. -/
noncomputable def continuousPart (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω)
    [SigmaFiniteFiltration P 𝓕] : ι → Ω → E :=
  if hX : IsAESquareIntegrable X 𝓕 P
    then continuousSquareIntegrable.out
      ((continuousSquareIntegrable ι E P 𝓕).orthogonalProjectionOnto (.mk X hX))
    else 0

lemma continuousPart_congr (X Y : ι → Ω → E) (hXY : ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω) :
    continuousPart X 𝓕 P = continuousPart Y 𝓕 P := by
  by_cases hX : IsAESquareIntegrable X 𝓕 P
  · simp only [continuousPart, hX, ↓reduceDIte, hX.congr hXY]
    ext t ω
    congr 2
    rwa [SquareIntegrable.mk_eq_mk]
  simp [continuousPart, hX, (isAESquareIntegrable_congr hXY).not.1 hX]

lemma continuous_continuousPart (X : ι → Ω → E) (ω : Ω) :
    Continuous (continuousPart X 𝓕 P · ω) := by
  rw [continuousPart]
  split_ifs
  · exact continuous_out _ _
  simpa using continuous_const

variable (P 𝓕) in
noncomputable def discontinuousPart (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω)
    [SigmaFiniteFiltration P 𝓕] : ι → Ω → E :=
  fun t ω ↦ X t ω - (continuousPart X 𝓕 P t ω)

lemma discontinuousPart_def : discontinuousPart X 𝓕 P =
    (fun t ω ↦ X t ω - (continuousPart X 𝓕 P t ω)) := rfl

variable (ι E P 𝓕) in
noncomputable def discontinuousSquareIntegrable : Submodule ℝ (SquareIntegrable ι E P 𝓕) :=
  (continuousSquareIntegrable ι E P 𝓕).orthogonal

variable (𝓕 P) in
noncomputable def stoppedValue' [Nonempty ι] (u : ι → Ω → E) (τ : Ω → WithTop ι) : Ω → E :=
    fun ω => if τ ω = ⊤ then 𝓕.limitProcess u P ω else u (τ ω).untopA ω

variable (P 𝓕) in
def IsPurelyDiscontinuous [Bot ι] (X : ι → Ω → E) : Prop :=
  IsAESquareIntegrable X 𝓕 P ∧
  ∀ Y, IsAESquareIntegrable Y 𝓕 P → (∀ᵐ ω ∂P, Continuous (Y · ω)) →
    (∀ᵐ ω ∂P, ⟪X ⊥ ω, Y ⊥ ω⟫ = 0) ∧
    ∀ τ, IsStoppingTime 𝓕 τ → P[fun ω ↦ ⟪stoppedValue' P 𝓕 X τ ω, stoppedValue' P 𝓕 Y τ ω⟫] = 0

lemma test [Bot ι] (X : ι → Ω → E)

lemma stoppedProcess_continuousPart [Nonempty ι] (X : ι → Ω → E) (τ : Ω → WithTop ι) :
    ∀ᵐ ω ∂P, ∀ t, continuousPart (stoppedProcess X τ) 𝓕 P t ω =
      stoppedProcess (continuousPart X 𝓕 P) τ t ω := by
  sorry

attribute [to_fun] stoppedProcess_sub

lemma stoppedProcess_discontinuousPart [Nonempty ι] (X : ι → Ω → E) (τ : Ω → WithTop ι) :
    ∀ᵐ ω ∂P, ∀ t, discontinuousPart (stoppedProcess X τ) 𝓕 P t ω =
      stoppedProcess (discontinuousPart X 𝓕 P) τ t ω := by
  filter_upwards [stoppedProcess_continuousPart X τ (𝓕 := 𝓕)] with ω h t
  rw [discontinuousPart, h, discontinuousPart_def, fun_stoppedProcess_sub]

variable [OrderTopology ι] [OrderBot ι]

open scoped Classical in
noncomputable def continuousPart' (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω)
    [SigmaFiniteFiltration P 𝓕] : ι → Ω → E :=
  if hX : IsLocallySquareIntegrable X 𝓕 P
    then fun t ω ↦ limUnder atTop (fun n ↦ continuousPart (stoppedProcess X (hX.choose n)) 𝓕 P t ω)
    else 0

lemma continuous_continuousPart' {X : ι → Ω → E} (hX : IsLocallySquareIntegrable X 𝓕 P) :
    ∀ᵐ ω ∂P, Continuous (continuousPart' X 𝓕 P · ω) := by
  have hτ1 := hX.choose_spec.1
  have hτ2 := hX.choose_spec.2
  set τ := hX.choose with h3
  have : ∀ᵐ ω ∂P, ∀ N, ∀ k, ∀ t,
      continuousPart (stoppedProcess (stoppedProcess X (τ k)) (τ N)) 𝓕 P t ω =
        stoppedProcess (continuousPart (stoppedProcess X (τ k)) 𝓕 P) (τ N) t ω := by
    rw [ae_all_iff]
    intro N
    rw [ae_all_iff]
    intro k
    filter_upwards [stoppedProcess_continuousPart (stoppedProcess X (τ k)) (τ N) (𝓕 := 𝓕)]
    grind
  filter_upwards [hτ1.tendsto_top, hτ1.mono, this] with ω hω hω' hω''
  rw [continuous_iff_continuousAt]
  intro t
  have h1 := (WithTop.tendsto_nhds_top_iff (τ · ω)).1 hω t
  obtain ⟨N, hN⟩ := eventually_atTop.1 h1
  have (s : ι) (hs : s ≤ τ N ω) : continuousPart' X 𝓕 P s ω =
      continuousPart (stoppedProcess X (τ N)) 𝓕 P s ω := by
    rw [continuousPart', dif_pos hX]
    apply Filter.Tendsto.limUnder_eq
    apply tendsto_nhds_of_eventually_eq
    rw [eventually_atTop]
    use N
    intro k hk
    have : ∀ᵐ ω ∂P, ∀ t, stoppedProcess X (τ N) t ω =
        stoppedProcess (stoppedProcess X (τ k)) (τ N) t ω := by
      filter_upwards [hτ1.mono] with ω hω t
      simp only [stoppedProcess]
      rw [min_eq_left (b := τ k ω)]
      · simp
      obtain h1 | h1 := eq_or_ne (τ k ω) ⊤
      · simp [h1]
      rw [← WithTop.le_untopA_iff h1]
      apply WithTop.untopA_mono h1
      grw [min_le_right]
      exact hω hk
    rw [continuousPart_congr _ _ this, hω'', stoppedProcess, min_eq_left]
    simp
    rfl
    grind
  refine (continuous_continuousPart (stoppedProcess X (τ N)) ω (𝓕 := 𝓕) (P := P)).continuousAt.congr ?_
  unfold Filter.EventuallyEq
  rw [eventually_nhds_iff]
  obtain h2 | h2 := eq_or_ne (τ N ω) ⊤
  · use Set.univ
    simp
    intro s
    rw [this]
    simp [h2]
  use Set.Iio (τ N ω).untopA
  refine ⟨?_, isOpen_Iio, ?_⟩
  · intro s (hs : s < _)
    rw [WithTop.lt_untopA_iff h2] at hs
    simp [this s hs.le]
  · rw [Set.mem_Iio, WithTop.lt_untopA_iff h2]
    exact hN N le_rfl



end Hilbert

end ProbabilityTheory
