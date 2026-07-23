/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Auxiliary.AEEq
public import BrownianMotion.Auxiliary.Indistinguishable
public import BrownianMotion.Auxiliary.Martingale
public import BrownianMotion.StochasticIntegral.LocalMartingale
public import Mathlib.Probability.Notation

import BrownianMotion.Auxiliary.Analysis
import BrownianMotion.Auxiliary.LimitProcess
import BrownianMotion.Gaussian.StochasticProcesses
import BrownianMotion.StochasticIntegral.ClassD
import BrownianMotion.StochasticIntegral.DoobLp
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.MeasureTheory.Function.Holder

/-! # Square integrable martingales

-/

@[expose] public section

open MeasureTheory Filter Function TopologicalSpace AEEqProcess
open scoped ENNReal Topology RealInnerProductSpace

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι] [TopologicalSpace ι] [NormedAddCommGroup E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ι → Ω → E} {𝓕 : Filtration ι mΩ}

section NormedSpace

variable [NormedSpace ℝ E]

/-- A square integrable martingale is a martingale with cadlag paths and uniformly bounded
second moments. -/
structure IsSquareIntegrable (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) : Prop where
  martingale : Martingale X 𝓕 P
  cadlag : ∀ ω, IsCadlag (X · ω)
  bounded : ⨆ i, eLpNorm (X i) 2 P < ∞

lemma IsSquareIntegrable.const [IsFiniteMeasure P] {c : E} :
    IsSquareIntegrable (fun _ _ ↦ c) 𝓕 P where
  martingale := martingale_const 𝓕 P c
  cadlag ω := isCadlag_const c
  bounded := by
    obtain _ | _ := isEmpty_or_nonempty ι
    · simp
    obtain rfl | hP := eq_or_ne P 0
    · simp
    rw [iSup_const, eLpNorm_const c (by simp) hP]
    finiteness

lemma IsSquareIntegrable.uniformIntegrable (hX : IsSquareIntegrable X 𝓕 P) :
    UniformIntegrable X 1 P := by
  sorry

/-- An a.e.-square integrable martingale is a process that is indistinguishable from a
square integrable martingale, see `IsSquareIntegrable`. -/
def IsAESquareIntegrable (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) : Prop :=
  ∃ Y : ι → Ω → E, IsSquareIntegrable Y 𝓕 P ∧ X ≡ᵐ[P] Y

lemma IsAESquareIntegrable.uniformIntegrable (hX : IsAESquareIntegrable X 𝓕 P) :
    UniformIntegrable X 1 P :=
  hX.choose_spec.1.uniformIntegrable.ae_eq (fun t ↦ (hX.choose_spec.2.ae_eq_eval t).symm)

lemma IsAESquareIntegrable.aestronglyAdapted (hX : IsAESquareIntegrable X 𝓕 P) :
    AEStronglyAdapted X 𝓕 P :=
  hX.choose_spec.1.martingale.stronglyAdapted.aestronglyAdapted.congr hX.choose_spec.2.symm

lemma IsSquareIntegrable.isAESquareIntegrable (hX : IsSquareIntegrable X 𝓕 P) :
    IsAESquareIntegrable X 𝓕 P := ⟨X, hX, by rfl⟩

lemma IsAESquareIntegrable.const [IsFiniteMeasure P] {c : E} :
    IsAESquareIntegrable (fun _ _ ↦ c) 𝓕 P :=
  IsSquareIntegrable.const.isAESquareIntegrable

lemma IsAESquareIntegrable.congr {X Y : ι → Ω → E} (hX : IsAESquareIntegrable X 𝓕 P)
    (hXY : X ≡ᵐ[P] Y) : IsAESquareIntegrable Y 𝓕 P := by
  obtain ⟨Z, hZ1, hZ2⟩ := hX
  exact ⟨Z, hZ1, hXY.symm.trans hZ2⟩

lemma isAESquareIntegrable_congr {X Y : ι → Ω → E} (hXY : X ≡ᵐ[P] Y) :
    IsAESquareIntegrable X 𝓕 P ↔ IsAESquareIntegrable Y 𝓕 P where
  mp h := h.congr hXY
  mpr h := h.congr hXY.symm

lemma IsSquareIntegrable.const_fun [OrderBot ι] {ξ : Ω → E} (mξ : StronglyMeasurable[𝓕 ⊥] ξ)
    [SigmaFiniteFiltration P 𝓕] (hξ1 : Integrable ξ P) (hξ2 : MemLp ξ 2 P) :
    IsSquareIntegrable (fun _ ↦ ξ) 𝓕 P where
  martingale := martingale_const_fun 𝓕 P mξ hξ1
  cadlag := fun _ ↦ isCadlag_const _
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

lemma IsSquareIntegrable.memLp_two (hX : IsSquareIntegrable X 𝓕 P) (i : ι) :
    MemLp (X i) 2 P := by
  refine ⟨(hX.martingale.stronglyMeasurable i).aestronglyMeasurable.mono (𝓕.le i), ?_⟩
  grw [le_iSup (fun t ↦ eLpNorm (X t) 2 P)]
  exact hX.bounded

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
  refine ⟨hX.martingale.add hY.martingale, fun ω ↦ (hX.cadlag ω).add (hY.cadlag ω), ?_⟩
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
lemma IsAESquareIntegrable.add [CompleteSpace E] (hX : IsAESquareIntegrable X 𝓕 P)
    (hY : IsAESquareIntegrable Y 𝓕 P) :
    IsAESquareIntegrable (X + Y) 𝓕 P := by
  obtain ⟨Z, hZ1, hZ2⟩ := hX
  obtain ⟨T, hT1, hT2⟩ := hY
  exact ⟨Z + T, hZ1.add hT1, hZ2.add hT2⟩

@[to_fun]
lemma IsSquareIntegrable.smul [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P) (r : ℝ) :
    IsSquareIntegrable (r • X) 𝓕 P where
  martingale := hX.martingale.smul r
  cadlag ω := hX.cadlag ω |>.const_smul r
  bounded := by
    change (⨆ i, eLpNorm (r • X i) 2 P) < ∞
    simp only [eLpNorm_const_smul, ← ENNReal.mul_iSup]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hX.bounded

@[to_fun]
lemma IsAESquareIntegrable.smul [CompleteSpace E] (hX : IsAESquareIntegrable X 𝓕 P) (r : ℝ) :
    IsAESquareIntegrable (r • X) 𝓕 P := by
  obtain ⟨Y, hY1, hY2⟩ := hX
  exact ⟨r • Y, hY1.smul r, hY2.const_smul⟩

@[to_fun]
lemma IsSquareIntegrable.neg [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P) :
    IsSquareIntegrable (-X) 𝓕 P := by
  simpa using hX.smul (-1)

@[to_fun]
lemma IsAESquareIntegrable.neg [CompleteSpace E] (hX : IsAESquareIntegrable X 𝓕 P) :
    IsAESquareIntegrable (-X) 𝓕 P := by
  simpa using hX.smul (-1)

@[to_fun]
lemma IsSquareIntegrable.sub [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P)
    (hY : IsSquareIntegrable Y 𝓕 P) :
    IsSquareIntegrable (X - Y) 𝓕 P := by
  simpa [sub_eq_add_neg] using (hX.add hY.neg)

@[to_fun]
lemma IsAESquareIntegrable.sub [CompleteSpace E] (hX : IsAESquareIntegrable X 𝓕 P)
    (hY : IsAESquareIntegrable Y 𝓕 P) :
    IsAESquareIntegrable (X - Y) 𝓕 P := by
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
      ∀ ω, IsCadlag (Y · ω)) 𝓕 (fun t ω ↦ ‖X t ω‖ ^ 2) P
  refine ⟨hX.localSeq, hX.isLocalizingSequence_localSeq, fun n ↦ ?_⟩
  have hXn := hX.stoppedProcess_localSeq n
  constructor
  · simpa [h_stopped_sq_norm] using hXn.submartingale_sq_norm
  · intro ω
    simpa [h_stopped_sq_norm] using IsCadlag.norm_sq (hXn.cadlag ω)

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

lemma _root_.MeasureTheory.UniformIntegrable.ae_tendsto_limitProcess
    (hX1 : UniformIntegrable X 1 P) (hX2 : Martingale X 𝓕 P) :
    ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (𝓕.limitProcess X P ω)) := by
  sorry

lemma IsSquareIntegrable.ae_tendsto_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (𝓕.limitProcess X P ω)) :=
  hX.uniformIntegrable.ae_tendsto_limitProcess hX.martingale

lemma IsAESquareIntegrable.ae_tendsto_limitProcess [Nonempty ι] (hX : IsAESquareIntegrable X 𝓕 P) :
    ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (𝓕.limitProcess X P ω)) := by
  filter_upwards [hX.choose_spec.2, hX.choose_spec.1.ae_tendsto_limitProcess,
    𝓕.limitProcess_congr hX.choose_spec.2] with ω h1 h2 h3
  rw [h3]
  exact h2.congr (fun t ↦ (h1 t).symm)

variable (𝓕) in
lemma tendsto_ae_condExp' (X : Ω → E) :
    ∀ᵐ ω ∂P, Tendsto (P[X | 𝓕 ·] ω) atTop (𝓝 (P[X | ⨆ t, 𝓕 t] ω)) := by
  sorry

lemma _root_.MeasureTheory.Martingale.condExp_limitProcess_ae_eq
    (hX1 : Martingale X 𝓕 P) (hX2 : UniformIntegrable X 1 P)
    (hX3 : ∀ ω, IsCadlag (X · ω)) (t : ι) :
    P[𝓕.limitProcess X P | 𝓕 t] =ᵐ[P] X t := by
  sorry

lemma IsAESquareIntegrable.condExp_limitProcess_ae_eq [CompleteSpace E] [Nonempty ι]
    (hX : IsAESquareIntegrable X 𝓕 P) (t : ι) :
    P[𝓕.limitProcess X P | 𝓕 t] =ᵐ[P] X t := by
  grw [hX.choose_spec.2.ae_eq_eval, condExp_congr_ae (𝓕.limitProcess_congr hX.choose_spec.2),
    hX.choose_spec.1.martingale.condExp_limitProcess_ae_eq hX.choose_spec.1.uniformIntegrable
      hX.choose_spec.1.cadlag]

variable (𝓕 P) in
noncomputable def stoppedValue' [Nonempty ι] (u : ι → Ω → E) (τ : Ω → WithTop ι) : Ω → E :=
    fun ω => if τ ω = ⊤ then 𝓕.limitProcess u P ω else u (τ ω).untopA ω

lemma IsAESquareIntegrable.condExp_limitProcess_ae_eq' [CompleteSpace E] [Nonempty ι]
    (hX : IsAESquareIntegrable X 𝓕 P) {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) :
    P[𝓕.limitProcess X P | hτ.measurableSpace] =ᵐ[P] stoppedValue' P 𝓕 X τ := by
  sorry

lemma IsSquareIntegrable.tendsto_eLpNorm_two_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    Tendsto (fun i ↦ eLpNorm (X i - 𝓕.limitProcess X P) 2 P) atTop (𝓝 0) := by
  sorry

lemma iSup_eLpNorm_le_eLpNorm_limitProcess (hX1 : Martingale X 𝓕 P)
    (hX2 : ∀ ω, IsCadlag (X · ω)) [IsFiniteMeasure P] [CompleteSpace E]
    (hX3 : UniformIntegrable X 1 P) :
    ⨆ t, eLpNorm (X t) 2 P ≤ eLpNorm (𝓕.limitProcess X P) 2 P := by
  apply iSup_le
  intro t
  rw [eLpNorm_congr_ae (hX1.condExp_limitProcess_ae_eq hX3 hX2 t).symm]
  exact eLpNorm_condExp_le_eLpNorm (by simp) (𝓕.limitProcess X P)

lemma isSquareIntegrable_of_limitProcess [CompleteSpace E] [IsFiniteMeasure P]
    (hX1 : Martingale X 𝓕 P) (hX2 : ∀ ω, IsCadlag (X · ω))
    (hX3 : UniformIntegrable X 1 P) (hX4 : MemLp (𝓕.limitProcess X P) 2 P) :
    IsSquareIntegrable X 𝓕 P where
  martingale := hX1
  cadlag := hX2
  bounded := by
    grw [iSup_eLpNorm_le_eLpNorm_limitProcess hX1 hX2 hX3]
    exact hX4.2

variable [CompleteSpace E] [IsFiniteMeasure P]

lemma IsSquareIntegrable.iSup_eLpNorm_eq_eLpNorm_limitProcess
    [Nonempty ι] [SeparableSpace ι] [OrderTopology ι] (hX : IsSquareIntegrable X 𝓕 P) :
    ⨆ i, eLpNorm (X i) 2 P = eLpNorm (𝓕.limitProcess X P) 2 P := by
  refine le_antisymm
    (iSup_eLpNorm_le_eLpNorm_limitProcess hX.martingale hX.cadlag hX.uniformIntegrable) ?_
  have := hX.isAESquareIntegrable.ae_tendsto_limitProcess
  calc
  _ ≤ atTop.liminf (fun t ↦ eLpNorm (X t) 2 P) := by
    grw [eLpNorm_eq_eLpNorm' (by simp) (by simp), Lp.eLpNorm'_lim_eq_lintegral_liminf this,
      lintegral_liminf_le]
    · rw [Monotone.map_liminf_of_continuousAt (f := fun x : ℝ≥0∞ ↦ x ^ (1 / ENNReal.toReal 2))]
      · apply liminf_le_liminf
        · apply Eventually.of_forall
          intro t
          simp [eLpNorm_eq_eLpNorm', eLpNorm']
        · isBoundedDefault
        · isBoundedDefault
      · intro x y hxy
        exact ENNReal.rpow_le_rpow hxy (by positivity)
      · exact ENNReal.continuous_rpow_const.continuousAt
    exact fun t ↦ ENNReal.continuous_rpow_const.measurable.comp <|
      (continuous_enorm.comp_stronglyMeasurable <|
        (hX.martingale.stronglyMeasurable t).mono (𝓕.le t)).measurable
  _ ≤ ⨆ i, eLpNorm (X i) 2 P := by
    rw [Filter.liminf_le_iff]
    intro x hx
    apply Frequently.of_forall
    intro t
    exact (le_iSup _ t).trans_lt hx

lemma IsSquareIntegrable.iSup_lpNorm_eq_lpNorm_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    ⨆ i, lpNorm (X i) 2 P = lpNorm (𝓕.limitProcess X P) 2 P := by
  sorry

lemma IsSquareIntegrable.memLp_limitProcess [Nonempty ι] [SeparableSpace ι] [OrderTopology ι]
    (hX : IsSquareIntegrable X 𝓕 P) :
    MemLp (𝓕.limitProcess X P) 2 P := by
  constructor
  · exact Filtration.stronglyMeasurable_limit_process'.aestronglyMeasurable
  rw [← hX.iSup_eLpNorm_eq_eLpNorm_limitProcess]
  exact hX.bounded

lemma IsAESquareIntegrable.memLp_limitProcess [Nonempty ι] [SeparableSpace ι] [OrderTopology ι]
    (hX : IsAESquareIntegrable X 𝓕 P) :
    MemLp (𝓕.limitProcess X P) 2 P := by
  sorry

lemma omg [MeasurableSpace ι] (hX : IsStronglyProgressive 𝓕 X) {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime 𝓕 τ) :
    StronglyMeasurable[hτ.measurableSpace] ({ω | τ ω = ⊤}.indicator (𝓕.limitProcess X P)) := by
  borelize E
  rw [stronglyMeasurable_iff_measurable_separable]
  constructor
  · intro s hs
    rw [hτ.measurableSet]
    constructor
    · sorry
    intro t
    have : MeasurableSet[𝓕 t] ({ω | 0 ∈ s} ∩ {ω | τ ω ≤ t}) := by
      by_cases h : 0 ∈ s
      · simp only [h, Set.setOf_true, Set.univ_inter]
        exact hτ t
      · simp [h]
    convert this using 1
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, and_congr_left_iff]
    intro h
    congrm ?_ ∈ s
    simp only [Set.indicator_apply_eq_zero, Set.mem_setOf_eq]
    intro h''
    rw [h''] at h
    contradiction
  · sorry

lemma stronglyMeasurable_stoppedValue' [MeasurableSpace ι] [Nonempty ι] [OrderTopology ι]
    [OrderBot ι] [SecondCountableTopology ι] [BorelSpace ι]
    (hX : IsStronglyProgressive 𝓕 X)
    (hRC : ∀ ω, IsRightContinuous (X · ω)) {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) :
    StronglyMeasurable[hτ.measurableSpace] (stoppedValue' P 𝓕 X τ) := by
  have : stoppedValue' P 𝓕 X τ = {ω | τ ω ≠ ⊤}.indicator (stoppedValue X τ) +
      {ω | τ ω = ⊤}.indicator (𝓕.limitProcess X P) := by
    ext ω
    simp only [stoppedValue', Pi.add_apply, Set.indicator, Set.mem_setOf_eq, stoppedValue]
    obtain h | h := eq_or_ne (τ ω) ⊤
    · simp [h]
    · simp [h]
  rw [this]
  borelize E
  refine .add ?_ ?_
  · apply StronglyMeasurable.indicator
    · exact Martingale.stronglyMeasurable_stoppedValue hX hRC hτ
    · sorry -- #42021
  · exact omg hX hτ

lemma IsSquareIntegrable.stronglyMeasurable_stoppedValue' [MeasurableSpace ι] [Nonempty ι]
    [OrderTopology ι] [OrderBot ι] [SecondCountableTopology ι] [BorelSpace ι]
    (hX : IsSquareIntegrable X 𝓕 P) {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) :
    StronglyMeasurable[hτ.measurableSpace] (stoppedValue' P 𝓕 X τ) :=
  ProbabilityTheory.stronglyMeasurable_stoppedValue'
    (hX.martingale.stronglyAdapted.isStronglyProgressive_of_rightContinuous
      (fun ω ↦ (hX.cadlag ω).right_continuous)) (fun ω ↦ (hX.cadlag ω).right_continuous) hτ

lemma IsAESquareIntegrable.aestronglyMeasurable_stoppedValue' [MeasurableSpace ι] [Nonempty ι]
    [OrderTopology ι] [OrderBot ι] [SecondCountableTopology ι] [BorelSpace ι]
    (hX : IsAESquareIntegrable X 𝓕 P) {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) :
    AEStronglyMeasurable[hτ.measurableSpace] (stoppedValue' P 𝓕 X τ) P := by
  refine ⟨stoppedValue' P 𝓕 hX.choose τ, hX.choose_spec.1.stronglyMeasurable_stoppedValue' hτ, ?_⟩
  filter_upwards [hX.choose_spec.2, 𝓕.limitProcess_congr hX.choose_spec.2] with ω h1 h2
  simp_all [stoppedValue']

lemma IsAESquareIntegrable.memLp_two_stoppedValue' [Nonempty ι]
    (τ : Ω → WithTop ι) (hX : IsAESquareIntegrable X 𝓕 P) :
    MemLp (stoppedValue' P 𝓕 X τ) 2 P := by
  sorry

lemma IsSquareIntegrable.stoppedProcess [OrderTopology ι] [OrderBot ι] [MeasurableSpace ι]
  [SecondCountableTopology ι] [BorelSpace ι] [MeasurableSpace E]
  [BorelSpace E] [MetrizableSpace ι] [Approximable 𝓕 P] (hX : IsSquareIntegrable X 𝓕 P)
    {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) :
    IsSquareIntegrable (stoppedProcess X τ) 𝓕 P := by
  apply isSquareIntegrable_of_limitProcess
  · exact hX.martingale.stoppedProcess (fun _ ↦ (hX.cadlag _).right_continuous) hτ
  · simp_rw [MeasureTheory.stoppedProcess]
    intro ω
    obtain h | hτ' := eq_or_ne (τ ω) ⊤
    · simpa [h] using hX.cadlag ω
    have (x : ι) : (min ↑x (τ ω)).untopA = min x (τ ω).untopA := by
      obtain h | h := le_total x (τ ω).untopA
      · rw [min_eq_left h, min_eq_left ((WithTop.le_untopA_iff hτ').1 h)]
        simp
      · rw [min_eq_right ((WithTop.untopA_le_iff hτ').1 h), min_eq_right h]
    simp_rw [this]
    constructor
    · intro t
      obtain ht | ht := lt_or_ge ↑t (τ ω)
      · convert (hX.cadlag ω).right_continuous (min t (τ ω).untopA) |>.comp
          (f := fun x : ι ↦ (min x (τ ω).untopA)) ?_ ?_
        · simp
        · fun_prop
        intro s hs
        simp_all [WithTop.lt_untopA_iff]
      refine (continuous_const (y := X (τ ω).untopA ω)).continuousWithinAt.congr ?_ ?_
      · grind
      · simp_all [WithTop.untopA_le_iff]
    · intro t
      obtain ht | ht := le_or_gt ↑t (τ ω)
      · obtain ⟨l, hl⟩ := (hX.cadlag ω).left_limit t
        refine ⟨l, hl.congr' ?_⟩
        refine Set.EqOn.eventuallyEq_nhdsWithin ?_
        intro s hs
        simp only
        rw [min_eq_left]
        exact hs.le.trans <| (WithTop.le_untopA_iff hτ').2 ht
      refine ⟨X (τ ω).untopA ω, tendsto_const_nhds.congr' ?_⟩
      refine eventuallyEq_nhdsWithin_iff.mpr ?_
      rw [eventually_nhds_iff]
      refine ⟨Set.Ioi (τ ω).untopA, ?_, ?_, ?_⟩
      · intro s hs1 hs2
        simp_all [min_eq_right hs1.le]
      · exact isOpen_Ioi
      · exact (WithTop.untopA_lt_iff hτ').2 ht
  · have : ClassD X 𝓕 P := hX.martingale.classD_iff_uniformIntegrable
      (fun ω ↦ (hX.cadlag ω).right_continuous) |>.2 hX.uniformIntegrable
    simp_rw [stoppedProcess_eq_stoppedValue]
    refine this.uniformIntegrable.comp (fun t : ι ↦ ⟨fun ω ↦ min t (τ ω),
        (isStoppingTime_const 𝓕 t).min hτ, ?_⟩)
    simp
  · refine ⟨Filtration.stronglyMeasurable_limit_process'.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by simp) (by simp)]
    calc
    ∫⁻ ω, ‖𝓕.limitProcess (MeasureTheory.stoppedProcess X τ) P ω‖ₑ ^ (ENNReal.toReal 2) ∂P
      = ∫⁻ ω, ‖stoppedValue' P 𝓕 X τ ω‖ₑ ^ (ENNReal.toReal 2) ∂P := by
      apply lintegral_congr_ae
      refine EventuallyEq.fun_comp ?_ (‖·‖ₑ ^ _)
      apply Filtration.limitProcess_ae_eq
      · have main : MeasurableSet[⨆ t, 𝓕 t] {ω | τ ω = ⊤} := by
          obtain ⟨s, hs⟩ := exists_seq_tendsto (atTop (α := ι))
          have : {ω | τ ω = ⊤} = ⋂ n, {ω | τ ω ≤ s n}ᶜ := by
            ext ω
            simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff, not_le]
            refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
            · simp [h]
            by_contra! h'
            simp_rw [← WithTop.lt_untopA_iff h'] at h
            have := eventually_ge_atTop (τ ω).untopA
            have := hs.eventually this
            obtain ⟨t, ht⟩ := this.exists
            grind
          rw [this]
          refine .iInter fun n ↦ .compl ?_
          exact (le_iSup (𝓕 ·) (s n)) _ (hτ.measurableSet_le (s n))
        apply StronglyMeasurable.ite
        · exact main
        · exact Filtration.stronglyMeasurable_limitProcess
        refine Martingale.stronglyMeasurable_stoppedValue
          (hX.martingale.stronglyAdapted.isStronglyProgressive_of_rightContinuous
            (fun ω ↦ (hX.cadlag ω).right_continuous)) (fun ω ↦ (hX.cadlag ω).right_continuous) hτ
            |>.mono ?_
        sorry
      filter_upwards [hX.isAESquareIntegrable.ae_tendsto_limitProcess] with ω h1
      simp only [MeasureTheory.stoppedProcess, stoppedValue']
      split_ifs with h
      · simpa [h]
      refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨(τ ω).untopA, fun t ht ↦ ?_⟩)
      simp [min_eq_right <| (WithTop.untopA_le_iff h).1 ht]
    _ ≤ ∫⁻ ω, (⨆ t, ‖X t ω‖ₑ) ^ (ENNReal.toReal 2) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hX.isAESquareIntegrable.ae_tendsto_limitProcess] with ω h1
      obtain h | h := eq_or_ne (τ ω) ⊤
      · simp only [stoppedValue', h, ↓reduceIte]
        grw [← ((continuous_enorm.tendsto (𝓕.limitProcess X P ω)).comp h1).limsup_eq,
          limsup_le_iSup]
        simp
      · gcongr
        simp only [stoppedValue', h, ↓reduceIte]
        exact le_iSup (fun t ↦ ‖X t ω‖ₑ) (τ ω).untopA
    _ ≤ 4 * ∫⁻ ω, ‖𝓕.limitProcess X P ω‖ₑ ^ (ENNReal.toReal 2) ∂P := by
      grw [integral_iSup_norm_rpow_le' hX.martingale
        (fun ω ↦ (hX.cadlag ω).right_continuous) (by simp)]
      gcongr
      simp
      norm_num
    _ < ∞ := by
      apply ENNReal.mul_lt_top (by simp)
      rw [← eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by simp) (by simp)]
      exact hX.memLp_limitProcess.2

lemma IsAESquareIntegrable.stoppedProcess [OrderTopology ι] [OrderBot ι] [MeasurableSpace ι]
  [SecondCountableTopology ι] [BorelSpace ι] [MeasurableSpace E]
  [BorelSpace E] [MetrizableSpace ι] [Approximable 𝓕 P] (hX : IsAESquareIntegrable X 𝓕 P)
    {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) :
    IsAESquareIntegrable (stoppedProcess X τ) 𝓕 P :=
  ⟨MeasureTheory.stoppedProcess hX.choose τ, hX.choose_spec.1.stoppedProcess hτ, by
    filter_upwards [hX.choose_spec.2] with ω h t
    simp [MeasureTheory.stoppedProcess, h]⟩

end NormedSpace

section Hilbert

variable [CompleteSpace E] [IsFiniteMeasure P]

section NormedSpace

variable [NormedSpace ℝ E]

variable (ι E P 𝓕) in
/-- The type of square integrable martingales. -/
def squareIntegrableSubmodule : Submodule ℝ (Ω →ₚ[P, 𝓕] E) where
  carrier := {X | IsAESquareIntegrable X 𝓕 P}
  add_mem' {X Y} hX hY := (hX.add hY).congr (coeFn_add X Y).symm
  zero_mem' := IsAESquareIntegrable.const.congr coeFn_zero.symm
  smul_mem' c {X} hX := (hX.smul c).congr (coeFn_smul c X).symm

variable (ι E P 𝓕) in
/-- The type of square integrable martingales. -/
def SquareIntegrable : Type _ := squareIntegrableSubmodule ι E P 𝓕

instance : AddCommGroup (SquareIntegrable ι E P 𝓕) :=
  AddSubgroupClass.toAddCommGroup (squareIntegrableSubmodule ι E P 𝓕)

instance : Module ℝ (SquareIntegrable ι E P 𝓕) :=
  Submodule.module (squareIntegrableSubmodule ι E P 𝓕)

/- This uses `sorry` because a martingale is not necessarily strongly measurable as a map from
`Ω` to `ι → E`. -/
/-- The equivalence class of a process that is indistinguishable from a square integrable
martingale. -/
noncomputable def SquareIntegrable.mk (X : ι → Ω → E) (hX : IsAESquareIntegrable X 𝓕 P) :
    SquareIntegrable ι E P 𝓕 :=
  ⟨.mk X hX.aestronglyAdapted, hX.congr (coeFn_mk X _).symm⟩

open scoped Classical in
/-- Given an equivalence class of square integrable martingales, this is a version that satisfies
`IsSquareIntegrable`. Don't use this directly, use the coercion system instead. -/
@[coe]
noncomputable def SquareIntegrable.out (X : SquareIntegrable ι E P 𝓕) : ι → Ω → E :=
  if h : ∃ Y, (∀ ω, Continuous (Y · ω)) ∧ IsSquareIntegrable Y 𝓕 P ∧ X.1 ≡ᵐ[P] Y
    then h.choose
    else X.2.choose

noncomputable instance : CoeFun (SquareIntegrable ι E P 𝓕) (fun _ ↦ ι → Ω → E) where
  coe := SquareIntegrable.out

lemma SquareIntegrable.isSquareIntegrable_coe (X : SquareIntegrable ι E P 𝓕) :
    IsSquareIntegrable X 𝓕 P := by
  rw [out]
  split_ifs with h
  · exact h.choose_spec.2.1
  · exact X.2.choose_spec.1

lemma SquareIntegrable.val_indist_coe (X : SquareIntegrable ι E P 𝓕) :
    X.1 ≡ᵐ[P] ↑X := by
  rw [out]
  split_ifs with h
  · exact h.choose_spec.2.2
  · exact X.2.choose_spec.2

@[ext]
lemma SquareIntegrable.ext {X Y : SquareIntegrable ι E P 𝓕} (h : ↑X ≡ᵐ[P] ↑Y) :
    X = Y := by
  unfold SquareIntegrable
  ext
  grw [val_indist_coe, val_indist_coe, h]

lemma SquareIntegrable.coe_add (X Y : SquareIntegrable ι E P 𝓕) :
    ↑(X + Y) ≡ᵐ[P] ↑X + ↑Y := by
  unfold SquareIntegrable
  grw [← val_indist_coe, Submodule.coe_add, coeFn_add, val_indist_coe, val_indist_coe]

lemma SquareIntegrable.coe_sub (X Y : SquareIntegrable ι E P 𝓕) :
    ↑(X - Y) ≡ᵐ[P] ↑X - ↑Y := by
  unfold SquareIntegrable
  grw [← val_indist_coe, Submodule.coe_sub, coeFn_sub, val_indist_coe, val_indist_coe]

lemma SquareIntegrable.coe_smul (X : SquareIntegrable ι E P 𝓕) (c : ℝ) :
    ↑(c • X) ≡ᵐ[P] c • ↑X := by
  unfold SquareIntegrable
  grw [← val_indist_coe, Submodule.coe_smul, coeFn_smul, val_indist_coe]

lemma SquareIntegrable.coe_neg (X : SquareIntegrable ι E P 𝓕) :
    ↑(-X) ≡ᵐ[P] -↑X := by
  unfold SquareIntegrable
  grw [← val_indist_coe, Submodule.coe_neg, coeFn_neg, val_indist_coe]

lemma SquareIntegrable.val_mk (X : ι → Ω → E) (hX : IsAESquareIntegrable X 𝓕 P)
    (h : AEStronglyAdapted X 𝓕 P) :
    (mk X hX).1 = .mk X h := rfl

/- This uses `sorry` because a martingale is not necessarily strongly measurable as a map from
`Ω` to `ι → E`. -/
lemma SquareIntegrable.mk_indist {X : ι → Ω → E} (hX : IsAESquareIntegrable X 𝓕 P) :
    mk X hX ≡ᵐ[P] X := by
  grw [← val_indist_coe, val_mk X hX hX.aestronglyAdapted, coeFn_mk]

lemma SquareIntegrable.mk_eq_mk {X Y : ι → Ω → E} {hX : IsAESquareIntegrable X 𝓕 P}
    {hY : IsAESquareIntegrable Y 𝓕 P} :
    mk X hX = mk Y hY ↔ X ≡ᵐ[P] Y where
  mp h := by
    unfold SquareIntegrable at h
    rw [Subtype.ext_iff, mk, mk] at h
    rwa [AEEqProcess.mk_eq_mk] at h
  mpr h := by
    ext
    grw [mk_indist, mk_indist, h]

lemma SquareIntegrable.mk_add {hX : IsAESquareIntegrable X 𝓕 P}
    {hY : IsAESquareIntegrable Y 𝓕 P} :
    mk (X + Y) (hX.add hY) = mk X hX + mk Y hY := by
  ext
  grw [mk_indist, coe_add, mk_indist, mk_indist]

variable (E P 𝓕) in
lemma SquareIntegrable.coe_const (c : E) :
    (mk (fun _ _ ↦ c) .const : SquareIntegrable ι E P 𝓕) ≡ᵐ[P] (fun _ _ ↦ c) :=
  mk_indist _

variable (E P 𝓕) in
lemma SquareIntegrable.coe_zero :
    (0 : SquareIntegrable ι E P 𝓕) ≡ᵐ[P] 0 := by
  unfold SquareIntegrable
  grw [← val_indist_coe, Submodule.coe_zero, coeFn_zero]

@[to_fun limitProcess_fun_add]
lemma IsAESquareIntegrable.limitProcess_add {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : ι → Ω → E}
    [LinearOrder ι] [Nonempty ι] {𝓕 : Filtration ι mΩ} [NormedAddCommGroup E] [TopologicalSpace ι]
    [SigmaFiniteFiltration P 𝓕] [NormedSpace ℝ E]
    (hX : IsAESquareIntegrable X 𝓕 P) (hY : IsAESquareIntegrable Y 𝓕 P) :
    𝓕.limitProcess (X + Y) P =ᵐ[P] 𝓕.limitProcess X P + 𝓕.limitProcess Y P := by
  apply 𝓕.limitProcess_ae_eq
    (𝓕.stronglyMeasurable_limitProcess.add 𝓕.stronglyMeasurable_limitProcess)
  filter_upwards [hX.ae_tendsto_limitProcess, hY.ae_tendsto_limitProcess] with ω h1 h2 using
    h1.add h2

@[to_fun limitProcess_fun_sub]
lemma IsAESquareIntegrable.limitProcess_sub {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : ι → Ω → E}
    [LinearOrder ι] [Nonempty ι] {𝓕 : Filtration ι mΩ} [NormedAddCommGroup E] [TopologicalSpace ι]
    [SigmaFiniteFiltration P 𝓕] [NormedSpace ℝ E]
    (hX : IsAESquareIntegrable X 𝓕 P) (hY : IsAESquareIntegrable Y 𝓕 P) :
    𝓕.limitProcess (X - Y) P =ᵐ[P] 𝓕.limitProcess X P - 𝓕.limitProcess Y P := by
  apply 𝓕.limitProcess_ae_eq
    (𝓕.stronglyMeasurable_limitProcess.sub 𝓕.stronglyMeasurable_limitProcess)
  filter_upwards [hX.ae_tendsto_limitProcess, hY.ae_tendsto_limitProcess] with ω h1 h2 using
    h1.sub h2

open TopologicalSpace in
/-- Two modifications that are right-continuous are indistinguishable. -/
lemma indistinguishable_of_modification' {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : T → Ω → E} [TopologicalSpace E] [TopologicalSpace T]
    [SeparableSpace T] [T2Space E] [Preorder T]
    (hX : ∀ᵐ ω ∂P, IsRightContinuous (X · ω)) (hY : ∀ᵐ ω ∂P, IsRightContinuous (Y · ω))
    (h : ∀ t, X t =ᵐ[P] Y t) :
    X ≡ᵐ[P] Y := sorry

variable [Nonempty ι] [SeparableSpace ι] [OrderTopology ι]

variable (ι E P 𝓕) in
/-- The injection of square integrable martingales into the `L^2` given by `X ↦ X ∞`.
This is a `LinearIsometryEquiv` onto the subspace of functions that are strongly measurable
with respect to `⨆ t, 𝓕 t`, see `SquareIntegrable.toL2Isom`. -/
noncomputable def SquareIntegrable.toL2 : SquareIntegrable ι E P 𝓕 →ₗ[ℝ] Lp E 2 P where
  toFun X := (isSquareIntegrable_coe X).memLp_limitProcess.toLp
  map_add' X Y := by
    rw [MemLp.toLp_congr _ _ (𝓕.limitProcess_congr (coe_add X Y)),
      MemLp.toLp_congr _ _ (IsAESquareIntegrable.limitProcess_add _ _), MemLp.toLp_add]
    · exact (isSquareIntegrable_coe X).memLp_limitProcess.add
        (isSquareIntegrable_coe Y).memLp_limitProcess
    · exact isSquareIntegrable_coe X |>.isAESquareIntegrable
    · exact isSquareIntegrable_coe Y |>.isAESquareIntegrable
    · exact ((isSquareIntegrable_coe X).add (isSquareIntegrable_coe Y)).memLp_limitProcess
  map_smul' c X := by
    rw [MemLp.toLp_congr _ _ (𝓕.limitProcess_congr (coe_smul X c)),
      MemLp.toLp_congr _ _ (𝓕.limitProcess_smul _ _), MemLp.toLp_const_smul]
    · simp
    · exact (isSquareIntegrable_coe X).memLp_limitProcess
    · exact (isSquareIntegrable_coe X).memLp_limitProcess.const_smul c
    · exact ((isSquareIntegrable_coe X).smul c).memLp_limitProcess

lemma SquareIntegrable.toL2_def (X : SquareIntegrable ι E P 𝓕) :
    toL2 ι E P 𝓕 X = (isSquareIntegrable_coe X).memLp_limitProcess.toLp := rfl

lemma SquareIntegrable.toL2_ae_eq (X : SquareIntegrable ι E P 𝓕) :
    toL2 ι E P 𝓕 X =ᵐ[P] 𝓕.limitProcess X P := by
  rw [toL2_def]
  exact MemLp.coeFn_toLp _

lemma SquareIntegrable.injective_toL2 : Injective (toL2 ι E P 𝓕) := by
  rw [injective_iff_map_eq_zero]
  intro X hX
  rw [toL2_def, ← MemLp.toLp_zero, MemLp.toLp_eq_toLp_iff] at hX
  swap; · simp
  ext
  refine .trans ?_ (coe_zero _ _ _).symm
  refine indistinguishable_of_modification' ?_ ?_ fun t ↦ ?_
  · exact ae_of_all _ fun _ ↦ (isSquareIntegrable_coe _).cadlag _
      |>.right_continuous
  · exact ae_of_all _ fun _ ↦ isRightContinuous_const 0
  grw [show (0 : ι → Ω → E) t = 0 from rfl, ← lpNorm_eq_zero _ two_ne_zero, ← toReal_eLpNorm,
    ENNReal.toReal_eq_zero_iff]
  · left
    suffices eLpNorm (X t) 2 P ≤ 0 by simp_all
    grw [le_iSup fun s ↦ eLpNorm (X s) 2 P,
      (isSquareIntegrable_coe _).iSup_eLpNorm_eq_eLpNorm_limitProcess, nonpos_iff_eq_zero,
      ← ofReal_lpNorm, ENNReal.ofReal_eq_zero, lpNorm_congr hX, lpNorm_zero]
    exact (isSquareIntegrable_coe _).memLp_limitProcess
  · exact ((isSquareIntegrable_coe X).martingale.stronglyMeasurable
      t).aestronglyMeasurable.mono (𝓕.le t)
  · exact (isSquareIntegrable_coe X).memLp_two t

noncomputable instance SquareIntegrable.normedAddCommGroup :
    NormedAddCommGroup (SquareIntegrable ι E P 𝓕) :=
  NormedAddCommGroup.induced _ _ (toL2 ι E P 𝓕) injective_toL2

lemma SquareIntegrable.norm_def {X : SquareIntegrable ι E P 𝓕} :
    ‖X‖ = lpNorm (𝓕.limitProcess X P) 2 P := by
  change ‖toL2 ι E P 𝓕 X‖ = _
  rw [toL2_def, Lp.norm_toLp, lpNorm, if_pos]
  exact 𝓕.stronglyMeasurable_limit_process'.aestronglyMeasurable

lemma SquareIntegrable.enorm_def {X : SquareIntegrable ι E P 𝓕} :
    ‖X‖ₑ = eLpNorm (𝓕.limitProcess X P) 2 P := by
  rw [← ofReal_norm, norm_def, ofReal_lpNorm]
  exact (isSquareIntegrable_coe X).memLp_limitProcess

end NormedSpace

variable [InnerProductSpace ℝ E] [Nonempty ι] [SeparableSpace ι] [OrderTopology ι]

noncomputable instance SquareIntegrable.innerProductSpace :
    InnerProductSpace ℝ (SquareIntegrable ι E P 𝓕) :=
  InnerProductSpace.induced (toL2 ι E P 𝓕)

lemma SquareIntegrable.inner_def {X Y : SquareIntegrable ι E P 𝓕} :
    ⟪X, Y⟫ = P[fun ω ↦ ⟪𝓕.limitProcess X P ω, 𝓕.limitProcess Y P ω⟫] := by
  rw [inner_induced_eq, toL2_def, toL2_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (isSquareIntegrable_coe X).memLp_limitProcess,
    MemLp.coeFn_toLp (isSquareIntegrable_coe Y).memLp_limitProcess] with ω h1 h2
  simp_all

/-- Given a martingale `X`, this is a càdlàg martingale that is a modification of `X`. -/
def _root_.MeasureTheory.modif (X : ι → Ω → E) :
    ι → Ω → E := sorry

lemma _root_.MeasureTheory.isCadlag_modif (X : ι → Ω → E) (ω : Ω) :
    IsCadlag (modif X · ω) := sorry

lemma _root_.MeasureTheory.modification_modif (hX : Martingale X 𝓕 P) (t : ι) :
    modif X t =ᵐ[P] X t := sorry

lemma _root_.MeasureTheory.martingale_modif : Martingale (modif X) 𝓕 P := sorry

variable (𝓕) in
lemma isSquareIntegrable_modif_condExp {X : Ω → E} (hX : MemLp X 2 P) :
    IsSquareIntegrable (modif (fun t ↦ P[X | 𝓕 t])) 𝓕 P where
  martingale := martingale_modif
  cadlag := isCadlag_modif _
  bounded := by
    refine LE.le.trans_lt (iSup_le fun i ↦ ?_) hX.2
    grw [eLpNorm_congr_ae (modification_modif (martingale_condExp X 𝓕 P) i), eLpNorm_condExp_le]

/-- The `LinearIsometryEquiv` between square integrable martingales and
the type of `L^2` random variables that are strongly measurable with respect to `⨆ t, 𝓕 t`,
given by `X ↦ X ∞`. -/
noncomputable def SquareIntegrable.toL2Isom [OrderTopology ι] :
    SquareIntegrable ι E P 𝓕 ≃ₗᵢ[ℝ] lpMeas E ℝ (⨆ t, 𝓕 t) 2 P where
  toFun X := ⟨toL2 ι E P 𝓕 X, by {
    rw [mem_lpMeas_iff_aestronglyMeasurable, aestronglyMeasurable_congr (toL2_ae_eq X)]
    exact 𝓕.stronglyMeasurable_limitProcess.aestronglyMeasurable
  }⟩
  invFun X := mk (modif (fun t ↦ P[X.1 | 𝓕 t]))
    (isSquareIntegrable_modif_condExp 𝓕 (Lp.memLp X.1)).isAESquareIntegrable
  map_add' := by simp
  map_smul' := by simp
  left_inv X := by
    ext
    apply indistinguishable_of_modification'
    · exact ae_of_all _ fun _ ↦ ((isSquareIntegrable_coe _).cadlag _).right_continuous
    · exact ae_of_all _ fun _ ↦ ((isSquareIntegrable_coe _).cadlag _).right_continuous
    intro t
    filter_upwards [mk_indist
        (X := modif (fun t ↦ P[(isSquareIntegrable_coe X).memLp_limitProcess.toLp _ | 𝓕 t]))
        (isSquareIntegrable_modif_condExp 𝓕
          (isSquareIntegrable_coe X).memLp_limitProcess).isAESquareIntegrable,
      modification_modif (martingale_condExp
        ((isSquareIntegrable_coe X).memLp_limitProcess.toLp _) 𝓕 P) t,
      condExp_congr_ae ((isSquareIntegrable_coe X).memLp_limitProcess.coeFn_toLp),
      (isSquareIntegrable_coe X).martingale.condExp_limitProcess_ae_eq
        X.isSquareIntegrable_coe.uniformIntegrable X.isSquareIntegrable_coe.cadlag t] with
        ω h1 h2 h3 h4
    rw! [toL2_def, h1, h2, h3, h4]
    rfl
  right_inv X := by
    ext
    simp only
    grw [toL2_def, MemLp.coeFn_toLp]
    obtain ⟨u, hu⟩ := (atTop : Filter ι).exists_seq_tendsto
    have h1 : ∀ᵐ ω ∂P, ∀ n, modif (fun t ↦ P[X.1 | 𝓕 t]) (u n) ω = P[X.1 | 𝓕 (u n)] ω := by
      rw [ae_all_iff]
      exact fun _ ↦ modification_modif (martingale_condExp X.1 𝓕 P) _
    grw [𝓕.limitProcess_congr (mk_indist _)]
    filter_upwards [h1,
      (isSquareIntegrable_modif_condExp 𝓕
        (Lp.memLp X.1)).isAESquareIntegrable.ae_tendsto_limitProcess,
      tendsto_ae_condExp' 𝓕 X.1,
      condExp_of_aestronglyMeasurable' (iSup_le 𝓕.le) X.2
        ((Lp.memLp X.1).integrable (by simp))] with ω h1 h2 h3 h4
    rw [← h4]
    apply tendsto_nhds_unique ?_ (h3.comp hu)
    apply Tendsto.congr h1 (h2.comp hu)
  norm_map' X := rfl

instance SquareIntegrable.completeSpace :
    CompleteSpace (SquareIntegrable ι E P 𝓕) :=
  haveI : Fact (⨆ t, 𝓕 t ≤ mΩ) := ⟨iSup_le 𝓕.le⟩
  toL2Isom.toIsometryEquiv.completeSpace

variable (ι E P 𝓕) in
/-- The set of continuous square integrable martingales, as a submodule of the type of
square-integrable martingales, see `SquareIntegrable`. -/
def continuousSquareIntegrable : Submodule ℝ (SquareIntegrable ι E P 𝓕) where
  carrier := {X | ∃ Y : ι → Ω → E, (∀ ω, Continuous (Y · ω)) ∧ IsSquareIntegrable Y 𝓕 P ∧ X ≡ᵐ[P] Y}
  add_mem' := by
    rintro X Y ⟨X', hX1, hX2, hX3⟩ ⟨Y', hY1, hY2, hY3⟩
    refine ⟨X' + Y', fun ω ↦ (hX1 ω).add (hY1 ω), hX2.add hY2, ?_⟩
    grw [← hX3, ← hY3, SquareIntegrable.coe_add]
  zero_mem' := ⟨0, by fun_prop, .const, SquareIntegrable.coe_zero E P 𝓕⟩
  smul_mem' := by
    rintro c X ⟨X', hX1, hX2, hX3⟩
    refine ⟨c • X', fun ω ↦ (hX1 ω).const_smul c, hX2.smul c, ?_⟩
    grw [SquareIntegrable.coe_smul X c, hX3]

omit [Nonempty ι] [SeparableSpace ι] [OrderTopology ι] in
lemma continuous_coe {X : SquareIntegrable ι E P 𝓕} (hX : X ∈ continuousSquareIntegrable ι E P 𝓕)
    (ω : Ω) :
    Continuous (X · ω) := by
  have : ∃ Y : ι → Ω → E,
      (∀ ω, Continuous (Y · ω)) ∧ IsSquareIntegrable Y 𝓕 P ∧ X.1 ≡ᵐ[P] Y := by
    obtain ⟨Y, hY1, hY2, hY3⟩ := hX
    refine ⟨Y, hY1, hY2, ?_⟩
    grw [SquareIntegrable.val_indist_coe, hY3]
  rw [SquareIntegrable.out, dif_pos this]
  exact this.choose_spec.1 ω

open scoped Classical in
noncomputable def aux (X : ι → Ω → E) (hX : IsAESquareIntegrable X 𝓕 P) :
    ι → Ω → E :=
  fun t ω ↦ if Continuous (hX.choose · ω) then hX.choose t ω else 0

omit [CompleteSpace E] [IsFiniteMeasure P] [Nonempty ι] [SeparableSpace ι] [OrderTopology ι] in
lemma continuous_aux (hX : IsAESquareIntegrable X 𝓕 P) (ω : Ω) :
    Continuous (aux X hX · ω) := by
  simp_rw [aux]
  split_ifs with h
  · exact h
  · exact continuous_const

omit [CompleteSpace E] [IsFiniteMeasure P] [Nonempty ι] [SeparableSpace ι] [OrderTopology ι] in
lemma aux_indist (hX1 : ∀ᵐ ω ∂P, Continuous (X · ω)) (hX2 : IsAESquareIntegrable X 𝓕 P) :
    aux X hX2 ≡ᵐ[P] X := by
  filter_upwards [hX1, hX2.choose_spec.2] with ω h1 h2
  simp_rw [h2] at h1
  simp [aux, h1, h2]

lemma isSquareIntegrable_aux [h𝓕 : 𝓕.IsComplete P] (hX1 : ∀ᵐ ω ∂P, Continuous (X · ω))
    (hX2 : IsAESquareIntegrable X 𝓕 P) :
    IsSquareIntegrable (aux X hX2) 𝓕 P := by
  have obv : ∀ᵐ ω ∂P, Continuous (hX2.choose · ω) := by
    filter_upwards [hX2.choose_spec.2, hX1] with ω h h'
    simp_rw [← h]
    exact h'
  constructor
  · apply hX2.choose_spec.1.martingale.congr
    · intro t
      obtain ⟨f, hf⟩ := hX2.choose_spec.1.martingale.stronglyAdapted t
      let s := {ω | Continuous (hX2.choose · ω)}
      have hs : MeasurableSet[𝓕 t] s := by
        apply MeasurableSet.of_compl
        apply h𝓕.measurableSet_of_null
        exact obv
      refine ⟨fun n ↦ @SimpleFunc.piecewise Ω E (𝓕 t) s hs (f n) (@SimpleFunc.const Ω E (𝓕 t) 0),
        ?_⟩
      intro ω
      by_cases hω : Continuous (hX2.choose · ω)
      · simpa [s, hω, aux] using hf ω
      · simp [s, hω, aux]
    · intro t
      filter_upwards [obv] with ω h
      simp [aux, h]
  · exact fun ω ↦ (continuous_aux hX2 ω).isCadlag
  convert hX2.choose_spec.1.memLp_limitProcess.2
  rw [← hX2.choose_spec.1.iSup_eLpNorm_eq_eLpNorm_limitProcess]
  congr with i
  rw [eLpNorm_congr_ae ((aux_indist hX1 hX2).ae_eq_eval i),
    eLpNorm_congr_ae (hX2.choose_spec.2.ae_eq_eval i)]

lemma mem_continuousSquareIntegrable [𝓕.IsComplete P] {X : SquareIntegrable ι E P 𝓕}
    (hX : ∀ᵐ ω ∂P, Continuous (X · ω)) : X ∈ continuousSquareIntegrable ι E P 𝓕 := by
  use aux X (SquareIntegrable.isSquareIntegrable_coe X).isAESquareIntegrable,
    continuous_aux (SquareIntegrable.isSquareIntegrable_coe X).isAESquareIntegrable,
    isSquareIntegrable_aux hX (SquareIntegrable.isSquareIntegrable_coe X).isAESquareIntegrable,
    (aux_indist hX _).symm

variable [𝓕.IsComplete P]

-- lemma isSquareIntegrable_out (X : continuousSquareIntegrable ι E P 𝓕) :
--     IsSquareIntegrable (continuousSquareIntegrable.out X) 𝓕 P :=
--   X.2.choose_spec.2.1

-- lemma out_ae_eq (X : continuousSquareIntegrable ι E P 𝓕) :
--     (fun ω t ↦ continuousSquareIntegrable.out X t ω) =ᵐ[P] X.1.1 :=
--   X.2.choose_spec.2.2

theorem integral_iSup_norm_rpow_rpow_inv_le_limitProcess
    (hX : IsAESquareIntegrable X 𝓕 P) {p : ℝ} (hp : 1 < p) :
    (∫⁻ ω, ⨆ t, ‖X t ω‖ₑ ^ p ∂P) ^ (1 / p) ≤
      (.ofReal ((p / (p - 1)) : ℝ)) * eLpNorm (𝓕.limitProcess X P) 2 P := by
  sorry

lemma exists_subsequence_ae_tendsto_uniformly {M : ℕ → ι → Ω → E} {N : ι → Ω → E}
    [SecondCountableTopology ι]
    (hM : ∀ n, IsAESquareIntegrable (M n) 𝓕 P) (hN : IsAESquareIntegrable N 𝓕 P)
    (h : Tendsto (fun n ↦ eLpNorm (𝓕.limitProcess (M n) P - 𝓕.limitProcess N P) 2 P) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ᵐ ω ∂P, TendstoUniformly (fun n t ↦ M (φ n) t ω) (N · ω) atTop) := by
  have h1 : ∀ n, ∃ k, ∀ l ≥ k,
      eLpNorm (𝓕.limitProcess (M l) P - 𝓕.limitProcess N P) 2 P ≤ (1 / 2) ^ n := by
    rw [ENNReal.tendsto_atTop_zero] at h
    intro n
    have : ((1 : ℝ≥0∞) / 2) ^ n > 0 := by
      apply ENNReal.pow_pos
      apply ENNReal.div_pos
      · simp
      · simp
    exact h _ this
  obtain ⟨φ, mφ, hφ⟩ := extraction_forall_of_eventually' h1
  use φ, mφ
  have : ∫⁻ ω, ∑' n, ⨆ t, ‖M (φ n) t ω - N t ω‖ₑ ∂P < ∞ :=
    calc
    _ = ∑' n, ∫⁻ ω, ⨆ t, ‖M (φ n) t ω - N t ω‖ₑ ∂P := by
      rw [lintegral_tsum]
      intro n
      refine ⟨fun ω ↦ ⨆ t, ‖(hM (φ n)).choose t ω - hN.choose t ω‖ₑ, ?_, ?_⟩
      · suffices Measurable (⨆ t, fun ω ↦ ‖(hM (φ n)).choose t ω - hN.choose t ω‖ₑ) by
          convert this with ω
          simp
        apply measurable_iSup_of_rightContinuous
        · intro ω
          apply IsRightContinuous.continuous_comp (by fun_prop)
          unfold IsRightContinuous
          intro t
          apply ContinuousWithinAt.sub
          · exact ((hM (φ n)).choose_spec.1.cadlag ω).right_continuous t
          · exact (hN.choose_spec.1.cadlag ω).right_continuous t
        · intro t
          apply StronglyMeasurable.measurable <| continuous_enorm.comp_stronglyMeasurable ?_
          exact ((hM (φ n)).choose_spec.1.martingale.stronglyMeasurable t).mono (𝓕.le t) |>.sub
            <| (hN.choose_spec.1.martingale.stronglyMeasurable t).mono (𝓕.le t)
      · filter_upwards [(hM (φ n)).choose_spec.2, hN.choose_spec.2] with ω h1 h2
        simp_rw [h1, h2]
    _ ≤ ∑' n, (∫⁻ ω, ⨆ t, ‖M (φ n) t ω - N t ω‖ₑ ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) := by
      sorry
    _ ≤ 2 * ∑' n, eLpNorm (𝓕.limitProcess (M (φ n)) P - 𝓕.limitProcess N P) 2 P := by
      rw [← ENNReal.tsum_mul_left]
      gcongr
      grw [integral_iSup_norm_rpow_rpow_inv_le_limitProcess (𝓕 := 𝓕)]
      · norm_num
        rw [eLpNorm_congr_ae ((hM (φ n)).limitProcess_fun_sub hN)]
        rfl
      · exact (hM (φ n)).sub hN
      · simp
    _ ≤ 2 * ∑' n, (1 / 2 : ℝ≥0∞) ^ n := by
      gcongr
      exact hφ n
    _ < ∞ := by
      apply ENNReal.mul_lt_top
      · simp
      rw [ENNReal.tsum_geometric]
      simp
  have h : AEMeasurable (fun ω ↦ ∑' n, ⨆ t, ‖M (φ n) t ω - N t ω‖ₑ) P := by
    apply AEMeasurable.tsum fun n ↦ ?_
    refine ⟨fun ω ↦ ⨆ t, ‖(hM (φ n)).choose t ω - hN.choose t ω‖ₑ, ?_, ?_⟩
    · suffices Measurable (⨆ t, fun ω ↦ ‖(hM (φ n)).choose t ω - hN.choose t ω‖ₑ) by
        convert this with ω
        simp
      apply measurable_iSup_of_rightContinuous
      · intro ω
        apply IsRightContinuous.continuous_comp (by fun_prop)
        unfold IsRightContinuous
        intro t
        apply ContinuousWithinAt.sub
        · exact ((hM (φ n)).choose_spec.1.cadlag ω).right_continuous t
        · exact (hN.choose_spec.1.cadlag ω).right_continuous t
      · intro t
        apply StronglyMeasurable.measurable <| continuous_enorm.comp_stronglyMeasurable ?_
        exact ((hM (φ n)).choose_spec.1.martingale.stronglyMeasurable t).mono (𝓕.le t) |>.sub
          <| (hN.choose_spec.1.martingale.stronglyMeasurable t).mono (𝓕.le t)
    · filter_upwards [(hM (φ n)).choose_spec.2, hN.choose_spec.2] with ω h1 h2
      simp_rw [h1, h2]
  filter_upwards [ae_lt_top' h this.ne] with ω h
  have := ENNReal.tendsto_atTop_zero_of_tsum_ne_top h.ne
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero] at this
  obtain ⟨n, hn⟩ := this (.ofReal (ε / 2)) (by simpa)
  rw [@eventually_atTop]
  use n
  intro k hk t
  rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by simp)]
  · rw [dist_comm, dist_eq_norm, ofReal_norm]
    grw [le_iSup (fun s ↦ ‖M (φ k) s ω - N s ω‖ₑ), hn k hk]
    rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg]
    · simpa
    positivity

/- Is in mathlib but not available here for some reason. -/
@[to_additive]
theorem tendsto_iff_enorm_div_tendsto_zero {α E : Type*} [SeminormedCommGroup E] {f : α → E}
    {a : Filter α} {b : E} :
    Tendsto f a (𝓝 b) ↔ Tendsto (fun e => ‖f e / b‖ₑ) a (𝓝 0) := by
  simp only [← edist_eq_enorm_div, ← tendsto_iff_edist_tendsto_0]

instance [SecondCountableTopology ι] :
    IsClosed (continuousSquareIntegrable ι E P 𝓕 : Set (SquareIntegrable ι E P 𝓕)) := by
  apply IsSeqClosed.isClosed
  intro M N hM1 hM2
  have :
      Tendsto (fun n ↦ eLpNorm (𝓕.limitProcess (M n) P - 𝓕.limitProcess N P) 2 P) atTop (𝓝 0) := by
    rw [tendsto_iff_enorm_sub_tendsto_zero] at hM2
    simp_rw [SquareIntegrable.enorm_def] at hM2
    refine hM2.congr fun n ↦ ?_
    rw [eLpNorm_congr_ae <| 𝓕.limitProcess_congr (SquareIntegrable.coe_sub (M n) N),
      eLpNorm_congr_ae (IsAESquareIntegrable.limitProcess_sub ?_ ?_)]
    all_goals exact SquareIntegrable.isSquareIntegrable_coe _ |>.isAESquareIntegrable
  obtain ⟨φ, mφ, hφ⟩ := exists_subsequence_ae_tendsto_uniformly
      (fun n ↦ SquareIntegrable.isSquareIntegrable_coe _ |>.isAESquareIntegrable)
      (SquareIntegrable.isSquareIntegrable_coe _ |>.isAESquareIntegrable) this
  apply mem_continuousSquareIntegrable
  filter_upwards [hφ] with ω h
  apply h.continuous
  exact Frequently.of_forall fun n ↦ continuous_coe (hM1 (φ n)) ω

variable [SecondCountableTopology ι]

open scoped Classical in
/-- The continuous martingale part of a square-integrable martingale `X`. This is defined as the
projection of `X` onto the closed subspace of continuous square-integrable martingales.

TODO: we rely on the already existing `AEEqFun` machinery, but this is about equivalence classes
of strongly measurable functions, while here we are interested in undistinguishability only
so measurablility is the way to go. It seems we will need to duplicate `AEEqFun` for the measurable
case. -/
noncomputable def continuousPart (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω)
    [IsFiniteMeasure P] [SigmaFiniteFiltration P 𝓕] [𝓕.IsComplete P] : ι → Ω → E :=
  if hX : IsAESquareIntegrable X 𝓕 P
    then (continuousSquareIntegrable ι E P 𝓕).starProjection (.mk X hX)
    else 0

lemma continuousPart_congr {X Y : ι → Ω → E} (hXY : X ≡ᵐ[P] Y) :
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
  · exact continuous_coe ((continuousSquareIntegrable ι E P 𝓕).starProjection_apply_mem _) ω
  simp [continuous_const]

lemma isSquareIntegrable_continuousPart {X : ι → Ω → E} :
    IsSquareIntegrable (continuousPart X 𝓕 P) 𝓕 P := by
  rw [continuousPart]
  split_ifs
  · exact SquareIntegrable.isSquareIntegrable_coe _
  · exact .const

variable (P 𝓕) in
noncomputable def discontinuousPart (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω)
    [IsFiniteMeasure P] [SigmaFiniteFiltration P 𝓕] [𝓕.IsComplete P] : ι → Ω → E :=
  X - continuousPart X 𝓕 P

lemma continuousPart_add_discontinuousPart :
    continuousPart X 𝓕 P + discontinuousPart X 𝓕 P = X := by
  simp [discontinuousPart]

variable (ι E P 𝓕) in
noncomputable def discontinuousSquareIntegrable : Submodule ℝ (SquareIntegrable ι E P 𝓕) :=
  (continuousSquareIntegrable ι E P 𝓕).orthogonal

variable (P 𝓕) in
def IsPurelyDiscontinuous (X : ι → Ω → E) : Prop :=
  IsAESquareIntegrable X 𝓕 P ∧
  ∀ Y, IsAESquareIntegrable Y 𝓕 P → (∀ᵐ ω ∂P, Continuous (Y · ω)) →
    P[fun ω ↦ ⟪𝓕.limitProcess X P ω, 𝓕.limitProcess Y P ω⟫] = 0

omit [CompleteSpace E] [IsFiniteMeasure P]
  [SeparableSpace ι] [OrderTopology ι] [𝓕.IsComplete P] [SecondCountableTopology ι] in
lemma IsPurelyDiscontinuous.congr (hX : IsPurelyDiscontinuous P 𝓕 X) (h : X ≡ᵐ[P] Y) :
    IsPurelyDiscontinuous P 𝓕 Y := by
  constructor
  · exact hX.1.congr h
  intro Z hZ1 hZ2
  rw [← hX.2 Z hZ1 hZ2]
  apply integral_congr_ae
  filter_upwards [𝓕.limitProcess_congr h] with ω h
  rw [h]

omit [𝓕.IsComplete P] [SecondCountableTopology ι] in
lemma mem_discontinuousSquareIntegrable {Y : SquareIntegrable ι E P 𝓕}
    (hY : IsPurelyDiscontinuous P 𝓕 Y) : Y ∈ discontinuousSquareIntegrable ι E P 𝓕 := by
  rw [discontinuousSquareIntegrable, Submodule.mem_orthogonal']
  intro X hX
  rw [SquareIntegrable.inner_def, hY.2]
  · exact X.isSquareIntegrable_coe.isAESquareIntegrable
  · exact ae_of_all _ <| continuous_coe hX

lemma isPurelyDiscontinuous_discontinuousPart {X : ι → Ω → E}
    (hX : IsAESquareIntegrable X 𝓕 P) :
    IsPurelyDiscontinuous P 𝓕 (discontinuousPart X 𝓕 P) := by
  constructor
  · exact hX.sub isSquareIntegrable_continuousPart.isAESquareIntegrable
  intro Y hY1 hY2
  have : ∀ᵐ ω ∂P, ⟪𝓕.limitProcess (discontinuousPart X 𝓕 P) P ω, 𝓕.limitProcess Y P ω⟫ =
      ⟪𝓕.limitProcess (SquareIntegrable.mk X hX -
        (continuousSquareIntegrable ι E P 𝓕).starProjection (.mk X hX)) P ω,
      𝓕.limitProcess (SquareIntegrable.mk Y hY1) P ω⟫ := by
    rw [discontinuousPart, continuousPart, dif_pos hX]
    filter_upwards [𝓕.limitProcess_congr ((SquareIntegrable.mk_indist hX).symm.sub .rfl),
      𝓕.limitProcess_congr (SquareIntegrable.coe_sub (.mk X hX) _),
      𝓕.limitProcess_congr (SquareIntegrable.mk_indist hY1)] with ω h1 h2 h3
    rw [h1, h2, h3]
  simp only
  rw [integral_congr_ae this, ← SquareIntegrable.inner_def,
    Submodule.starProjection_inner_eq_zero]
  apply mem_continuousSquareIntegrable
  filter_upwards [hY2, SquareIntegrable.mk_indist hY1] with ω h1 h2
  simp_rw [h2]
  exact h1

lemma test {X Y Z : ι → Ω → E} (hX1 : IsAESquareIntegrable X 𝓕 P)
    (hX2 : ∀ᵐ ω ∂P, Continuous (X · ω)) (hY1 : IsAESquareIntegrable Y 𝓕 P)
    (hY2 : IsPurelyDiscontinuous P 𝓕 Y) (hZ1 : IsAESquareIntegrable Z 𝓕 P)
    (hZ2 : Z ≡ᵐ[P] X + Y) :
    X ≡ᵐ[P] continuousPart Z 𝓕 P := by
  rw [← SquareIntegrable.mk_eq_mk (hX := hZ1) (hY := hX1.add hY1),
    SquareIntegrable.mk_add (hX := hX1) (hY := hY1)] at hZ2
  have h1 : .mk X hX1 ∈ continuousSquareIntegrable ι E P 𝓕 := by
    apply mem_continuousSquareIntegrable
    filter_upwards [hX2, SquareIntegrable.mk_indist hX1] with ω h1 h2
    simp_rw [h2]
    exact h1
  have h2 : .mk Y hY1 ∈ discontinuousSquareIntegrable ι E P 𝓕 := by
    apply mem_discontinuousSquareIntegrable
    exact hY2.congr (SquareIntegrable.mk_indist hY1).symm
  have := Submodule.eq_starProjection_of_mem_orthogonal' h1 h2 hZ2
  rw [continuousPart, dif_pos hZ1, this]
  exact SquareIntegrable.mk_indist hX1 |>.symm

lemma test2 {X Y Z : ι → Ω → E} (hX1 : IsAESquareIntegrable X 𝓕 P)
    (hX2 : ∀ᵐ ω ∂P, Continuous (X · ω)) (hY1 : IsAESquareIntegrable Y 𝓕 P)
    (hY2 : IsPurelyDiscontinuous P 𝓕 Y) (hZ1 : IsAESquareIntegrable Z 𝓕 P)
    (hZ2 : Z ≡ᵐ[P] X + Y) :
    Y ≡ᵐ[P] discontinuousPart Z 𝓕 P := by
  grw [discontinuousPart, ← test hX1 hX2 hY1 hY2 hZ1 hZ2, hZ2]
  simp

lemma limitProcess_stoppedProcess [MeasurableSpace ι] [OrderBot ι] [BorelSpace ι]
    {τ : Ω → WithTop ι}
    (hX1 : Martingale X 𝓕 P) (hX2 : UniformIntegrable X 1 P) (hX3 : ∀ ω, IsRightContinuous (X · ω))
    (hτ : IsStoppingTime 𝓕 τ) :
    𝓕.limitProcess (stoppedProcess X τ) P =ᵐ[P] stoppedValue' P 𝓕 X τ := by
  borelize E
  apply 𝓕.limitProcess_ae_eq
  · exact stronglyMeasurable_stoppedValue'
      (hX1.stronglyAdapted.isStronglyProgressive_of_rightContinuous hX3) hX3 hτ |>.mono sorry
      -- #42021
  filter_upwards [hX2.ae_tendsto_limitProcess hX1] with ω h
  obtain h1 | h1 := eq_or_ne (τ ω) ⊤
  · simpa [stoppedProcess, stoppedValue', h1]
  simp only [stoppedProcess, stoppedValue', h1, ↓reduceIte]
  refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨(τ ω).untopA, fun t ht ↦ ?_⟩)
  simp only
  rw [min_eq_right ((WithTop.untopA_le_iff h1).1 ht)]

lemma IsSquareIntegrable.limitProcess_stoppedProcess [MeasurableSpace ι] [OrderBot ι] [BorelSpace ι]
    {τ : Ω → WithTop ι}
    (hX : IsSquareIntegrable X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) :
    𝓕.limitProcess (MeasureTheory.stoppedProcess X τ) P =ᵐ[P] stoppedValue' P 𝓕 X τ :=
  ProbabilityTheory.limitProcess_stoppedProcess hX.martingale hX.uniformIntegrable
    (fun ω ↦ (hX.cadlag ω).right_continuous) hτ

lemma IsAESquareIntegrable.limitProcess_stoppedProcess
    [MeasurableSpace ι] [OrderBot ι] [BorelSpace ι] {τ : Ω → WithTop ι}
    (hX : IsAESquareIntegrable X 𝓕 P) (hτ : IsStoppingTime 𝓕 τ) :
    𝓕.limitProcess (MeasureTheory.stoppedProcess X τ) P =ᵐ[P] stoppedValue' P 𝓕 X τ := by
  sorry

lemma stoppedProcess_mem_continuousSquareIntegrable (hX : ∀ᵐ ω ∂P, Continuous (X · ω))
    (τ : Ω → WithTop ι) :
    ∀ᵐ ω ∂P, Continuous (stoppedProcess X τ · ω) := by
  filter_upwards [hX] with ω h
  simp only [stoppedProcess]
  obtain h | h := eq_or_ne (τ ω) ⊤
  · simpa [h]
  have (x : ι) : (min ↑x (τ ω)).untopA = min x (τ ω).untopA := by
    obtain h' | h' := le_total x (τ ω).untopA
    · rw [min_eq_left h', min_eq_left ((WithTop.le_untopA_iff h).1 h')]
      simp
    · rw [min_eq_right ((WithTop.untopA_le_iff h).1 h'), min_eq_right h']
  simp_rw [this]
  fun_prop

nonrec
lemma IsPurelyDiscontinuous.stoppedProcess [OrderBot ι] [MeasurableSpace ι] [BorelSpace ι]
    [MeasurableSpace E] [BorelSpace E] [MetrizableSpace ι] [Approximable 𝓕 P]
    (hX : IsPurelyDiscontinuous P 𝓕 X)
    {τ : Ω → WithTop ι} (hτ : IsStoppingTime 𝓕 τ) :
    IsPurelyDiscontinuous P 𝓕 (stoppedProcess X τ) := by
  refine ⟨hX.1.stoppedProcess hτ, fun Y hY1 hY2 ↦ ?_⟩
  calc
  ∫ ω, ⟪𝓕.limitProcess (stoppedProcess X τ) P ω, 𝓕.limitProcess Y P ω⟫ ∂P
    = ∫ ω, innerSL ℝ (stoppedValue' P 𝓕 X τ ω) (𝓕.limitProcess Y P ω) ∂P := by
    apply integral_congr_ae
    filter_upwards [hX.1.limitProcess_stoppedProcess hτ] with ω h
    simp [h]
  _ = ∫ ω, innerSL ℝ (stoppedValue' P 𝓕 X τ ω) (stoppedValue' P 𝓕 Y τ ω) ∂P := by
    rw [← integral_condExp hτ.measurableSpace_le]
    apply integral_congr_ae
    have h1 : Integrable (fun ω ↦ ⟪stoppedValue' P 𝓕 X τ ω, 𝓕.limitProcess Y P ω⟫) P := by
      rw [← memLp_one_iff_integrable]
      exact (innerSL ℝ).memLp_of_bilin 1 (hX.1.memLp_two_stoppedValue' τ)
        hY1.memLp_limitProcess
    filter_upwards [condExp_bilin_of_aestronglyMeasurable_left (innerSL ℝ)
        (hX.1.aestronglyMeasurable_stoppedValue' hτ) h1
        (hY1.memLp_limitProcess.integrable (by simp)),
        hY1.condExp_limitProcess_ae_eq' hτ] with ω h1 h2
    rw [← h2]
    exact h1
  _ = ∫ ω, innerSL ℝ (𝓕.limitProcess X P ω) (stoppedValue' P 𝓕 Y τ ω) ∂P := by
    nth_rw 2 [← integral_condExp hτ.measurableSpace_le]
    apply integral_congr_ae
    have h1 : Integrable (fun ω ↦ innerSL ℝ (𝓕.limitProcess X P ω) (stoppedValue' P 𝓕 Y τ ω)) P := by
      rw [← memLp_one_iff_integrable]
      exact (innerSL ℝ).memLp_of_bilin 1 hX.1.memLp_limitProcess
        (hY1.memLp_two_stoppedValue' τ)
    filter_upwards [condExp_bilin_of_aestronglyMeasurable_right (innerSL ℝ)
        (hY1.aestronglyMeasurable_stoppedValue' hτ) h1
        (hX.1.memLp_limitProcess.integrable (by simp)),
        hX.1.condExp_limitProcess_ae_eq' hτ] with ω h1 h2
    rw [← h2]
    exact h1.symm
  _ = ∫ ω, ⟪𝓕.limitProcess X P ω, 𝓕.limitProcess (stoppedProcess Y τ) P ω⟫ ∂P := by
    apply integral_congr_ae
    filter_upwards [hY1.limitProcess_stoppedProcess hτ] with w h
    simp [h]
  _ = 0 := by
    apply hX.2
    · exact hY1.stoppedProcess hτ
    · exact stoppedProcess_mem_continuousSquareIntegrable hY2 τ

variable (X 𝓕 P) in
lemma key (τ : Ω → WithTop ι) :
    stoppedProcess X τ =
      stoppedProcess (continuousPart X 𝓕 P) τ + stoppedProcess (discontinuousPart X 𝓕 P) τ := by
  nth_rw 1 [← continuousPart_add_discontinuousPart (X := X) (𝓕 := 𝓕) (P := P),
    stoppedProcess_add]

lemma stoppedProcess_continuousPart [OrderBot ι] [MeasurableSpace ι] [BorelSpace ι]
    [MetrizableSpace ι] [Approximable 𝓕 P]
    {X : ι → Ω → E} (hX : IsAESquareIntegrable X 𝓕 P) {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime 𝓕 τ) :
    continuousPart (stoppedProcess X τ) 𝓕 P ≡ᵐ[P]
      stoppedProcess (continuousPart X 𝓕 P) τ := by
  borelize E
  symm
  apply test (isSquareIntegrable_continuousPart.isAESquareIntegrable.stoppedProcess hτ)
    (stoppedProcess_mem_continuousSquareIntegrable (ae_of_all _ (continuous_continuousPart X)) τ)
    ((isPurelyDiscontinuous_discontinuousPart hX).1.stoppedProcess hτ)
    ((isPurelyDiscontinuous_discontinuousPart hX).stoppedProcess hτ)
    (hX.stoppedProcess hτ) (by rw [key P X 𝓕 τ])

attribute [to_fun] stoppedProcess_sub

lemma stoppedProcess_discontinuousPart [OrderBot ι] [MeasurableSpace ι] [BorelSpace ι]
    [MetrizableSpace ι] [Approximable 𝓕 P]
    {X : ι → Ω → E} (hX : IsAESquareIntegrable X 𝓕 P) {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime 𝓕 τ) :
    discontinuousPart (stoppedProcess X τ) 𝓕 P ≡ᵐ[P]
      stoppedProcess (discontinuousPart X 𝓕 P) τ := by
  borelize E
  symm
  apply test2 (isSquareIntegrable_continuousPart.isAESquareIntegrable.stoppedProcess hτ)
    (stoppedProcess_mem_continuousSquareIntegrable (ae_of_all _ (continuous_continuousPart X)) τ)
    ((isPurelyDiscontinuous_discontinuousPart hX).1.stoppedProcess hτ)
    ((isPurelyDiscontinuous_discontinuousPart hX).stoppedProcess hτ)
    (hX.stoppedProcess hτ) (by rw [key P X 𝓕 τ])

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
