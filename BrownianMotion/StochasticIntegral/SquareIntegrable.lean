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

/-- An a.e.-square integrable martingale is a process that is indistinguishable from a
square integrable martingale, see `IsSquareIntegrable`. -/
def IsAESquareIntegrable (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) : Prop :=
  ∃ Y : ι → Ω → E, IsSquareIntegrable Y 𝓕 P ∧ X ≡ᵐ[P] Y

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

lemma IsSquareIntegrable.ae_tendsto_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (𝓕.limitProcess X P ω)) := by
  sorry

variable (𝓕) in
lemma tendsto_ae_condExp' (X : Ω → E) :
    ∀ᵐ ω ∂P, Tendsto (P[X | 𝓕 ·] ω) atTop (𝓝 (P[X | ⨆ t, 𝓕 t] ω)) := by
  sorry

lemma IsSquareIntegrable.condExp_limitProcess_ae_eq (hX : IsSquareIntegrable X 𝓕 P) (t : ι) :
    P[𝓕.limitProcess X P | 𝓕 t] =ᵐ[P] X t := by
  sorry

lemma IsSquareIntegrable.tendsto_eLpNorm_two_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    Tendsto (fun i ↦ eLpNorm (X i - 𝓕.limitProcess X P) 2 P) atTop (𝓝 0) := by
  sorry

lemma IsSquareIntegrable.iSup_eLpNorm_eq_eLpNorm_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    ⨆ i, eLpNorm (X i) 2 P = eLpNorm (𝓕.limitProcess X P) 2 P := by
  sorry

lemma IsSquareIntegrable.iSup_lpNorm_eq_lpNorm_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    ⨆ i, lpNorm (X i) 2 P = lpNorm (𝓕.limitProcess X P) 2 P := by
  sorry

lemma IsSquareIntegrable.memLp_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    MemLp (𝓕.limitProcess X P) 2 P := by
  constructor
  · exact Filtration.stronglyMeasurable_limit_process'.aestronglyMeasurable
  rw [← hX.iSup_eLpNorm_eq_eLpNorm_limitProcess]
  exact hX.bounded

end NormedSpace

section Hilbert

variable [CompleteSpace E] [IsFiniteMeasure P]

section NormedSpace

variable [NormedSpace ℝ E]

variable (ι E P 𝓕) in
/-- The type of square integrable martingales.

TODO: we rely on the already existing `AEEqFun` machinery, but this is about equivalence classes
of strongly measurable functions, while here we are interested in indistinguishability only
so measurablility is the way to go. It seems we will need to duplicate `AEEqFun` for the measurable
case. -/
def SquareIntegrable : Submodule ℝ (Ω →ₚ[P, 𝓕] E) where
  carrier := {X | IsAESquareIntegrable X 𝓕 P}
  add_mem' {X Y} hX hY := (hX.add hY).congr (coeFn_add X Y).symm
  zero_mem' := IsAESquareIntegrable.const.congr coeFn_zero.symm
  smul_mem' c {X} hX := (hX.smul c).congr (coeFn_smul c X).symm

/- This uses `sorry` because a martingale is not necessarily strongly measurable as a map from
`Ω` to `ι → E`. -/
/-- The equivalence class of a process that is indistinguishable from a square integrable
martingale. -/
noncomputable def SquareIntegrable.mk (X : ι → Ω → E) (hX : IsAESquareIntegrable X 𝓕 P) :
    SquareIntegrable ι E P 𝓕 :=
  ⟨.mk X hX.aestronglyAdapted, ⟨hX.choose, hX.choose_spec.1, by grw [coeFn_mk, hX.choose_spec.2]⟩⟩

open scoped Classical in
/-- Given an equivalence class of square integrable martingales, this is a version that satisfies
`IsSquareIntegrable`. Don't use this directly, use the coercion system instead. -/
@[coe]
noncomputable def SquareIntegrable.out (X : SquareIntegrable ι E P 𝓕) : ι → Ω → E :=
  X.2.choose

noncomputable instance : CoeFun (SquareIntegrable ι E P 𝓕) (fun _ ↦ ι → Ω → E) where
  coe := SquareIntegrable.out

lemma SquareIntegrable.isSquareIntegrable_coe (X : SquareIntegrable ι E P 𝓕) :
    IsSquareIntegrable X 𝓕 P := X.2.choose_spec.1

lemma SquareIntegrable.val_indist_coe (X : SquareIntegrable ι E P 𝓕) :
    X.1 ≡ᵐ[P] ↑X := by
  grw [X.2.choose_spec.2]
  rfl

@[ext]
lemma SquareIntegrable.ext {X Y : SquareIntegrable ι E P 𝓕} (h : ↑X ≡ᵐ[P] ↑Y) :
    X = Y := by
  ext
  grw [val_indist_coe, val_indist_coe, h]

lemma SquareIntegrable.coe_add (X Y : SquareIntegrable ι E P 𝓕) :
    ↑(X + Y) ≡ᵐ[P] ↑X + ↑Y := by
  grw [← val_indist_coe, Submodule.coe_add, coeFn_add, val_indist_coe, val_indist_coe]

lemma SquareIntegrable.coe_smul (X : SquareIntegrable ι E P 𝓕) (c : ℝ) :
    ↑(c • X) ≡ᵐ[P] c • ↑X := by
  grw [← val_indist_coe, Submodule.coe_smul, coeFn_smul, val_indist_coe]

lemma SquareIntegrable.coe_neg (X : SquareIntegrable ι E P 𝓕) :
    ↑(-X) ≡ᵐ[P] -↑X := by
  grw [← val_indist_coe, Submodule.coe_neg, coeFn_neg, val_indist_coe]

lemma SquareIntegrable.val_mk (X : ι → Ω → E) (hX : IsAESquareIntegrable X 𝓕 P)
    (h : AEStronglyAdapted X 𝓕 P) :
    (mk X hX).1 = .mk X h := rfl

/- This uses `sorry` because a martingale is not necessarily strongly measurable as a map from
`Ω` to `ι → E`. -/
lemma SquareIntegrable.mk_ae_eq {X : ι → Ω → E} (hX : IsAESquareIntegrable X 𝓕 P) :
    mk X hX ≡ᵐ[P] X := by
  grw [← val_indist_coe, val_mk X hX hX.aestronglyAdapted, coeFn_mk]

lemma SquareIntegrable.mk_eq_mk {X Y : ι → Ω → E} {hX : IsAESquareIntegrable X 𝓕 P}
    {hY : IsAESquareIntegrable Y 𝓕 P} :
    mk X hX = mk Y hY ↔ X ≡ᵐ[P] Y where
  mp h := by
    rw [Subtype.ext_iff, mk, mk] at h
    rwa [AEEqProcess.mk_eq_mk] at h
  mpr h := by
    ext
    grw [mk_ae_eq, mk_ae_eq, h]

variable (E P 𝓕) in
lemma SquareIntegrable.coe_const (c : E) :
    (mk (fun _ _ ↦ c) .const : SquareIntegrable ι E P 𝓕) ≡ᵐ[P] (fun _ _ ↦ c) :=
  mk_ae_eq _

variable (E P 𝓕) in
lemma SquareIntegrable.coe_zero :
    (0 : SquareIntegrable ι E P 𝓕) ≡ᵐ[P] 0 := by
  grw [← val_indist_coe, Submodule.coe_zero, coeFn_zero]

@[to_fun limitProcess_fun_add]
lemma IsSquareIntegrable.limitProcess_add {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : ι → Ω → E}
    [LinearOrder ι] [Nonempty ι] {𝓕 : Filtration ι mΩ} [NormedAddCommGroup E] [TopologicalSpace ι]
    [SigmaFiniteFiltration P 𝓕] [NormedSpace ℝ E]
    (hX : IsSquareIntegrable X 𝓕 P) (hY : IsSquareIntegrable Y 𝓕 P) :
    𝓕.limitProcess (X + Y) P =ᵐ[P] 𝓕.limitProcess X P + 𝓕.limitProcess Y P := by
  apply 𝓕.limitProcess_ae_eq
    (𝓕.stronglyMeasurable_limitProcess.add 𝓕.stronglyMeasurable_limitProcess)
  filter_upwards [hX.ae_tendsto_limitProcess, hY.ae_tendsto_limitProcess] with ω h1 h2 using
    h1.add h2

open TopologicalSpace in
/-- Two modifications that are right-continuous are indistinguishable. -/
lemma indistinguishable_of_modification' {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : T → Ω → E} [TopologicalSpace E] [TopologicalSpace T]
    [SeparableSpace T] [T2Space E] [Preorder T]
    (hX : ∀ᵐ ω ∂P, IsRightContinuous (X · ω)) (hY : ∀ᵐ ω ∂P, IsRightContinuous (Y · ω))
    (h : ∀ t, X t =ᵐ[P] Y t) :
    X ≡ᵐ[P] Y := sorry

variable [Nonempty ι]

variable (ι E P 𝓕) in
/-- The injection of square integrable martingales into the `L^2` given by `X ↦ X ∞`.
This is a `LinearIsometryEquiv` onto the subspace of functions that are strongly measurable
with respect to `⨆ t, 𝓕 t`, see `SquareIntegrable.toL2Isom`. -/
noncomputable def SquareIntegrable.toL2 : SquareIntegrable ι E P 𝓕 →ₗ[ℝ] Lp E 2 P where
  toFun X := (isSquareIntegrable_coe X).memLp_limitProcess.toLp
  map_add' X Y := by
    rw [MemLp.toLp_congr _ _ (𝓕.limitProcess_congr (coe_add X Y)),
      MemLp.toLp_congr _ _ (IsSquareIntegrable.limitProcess_add _ _), MemLp.toLp_add]
    · exact (isSquareIntegrable_coe X).memLp_limitProcess.add
        (isSquareIntegrable_coe Y).memLp_limitProcess
    · exact isSquareIntegrable_coe X
    · exact isSquareIntegrable_coe Y
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

variable [SeparableSpace ι]

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

end NormedSpace

variable [InnerProductSpace ℝ E] [Nonempty ι] [SeparableSpace ι]

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
    filter_upwards [mk_ae_eq
        (X := modif (fun t ↦ P[(isSquareIntegrable_coe X).memLp_limitProcess.toLp _ | 𝓕 t]))
        (isSquareIntegrable_modif_condExp 𝓕
          (isSquareIntegrable_coe X).memLp_limitProcess).isAESquareIntegrable,
      modification_modif (martingale_condExp
        ((isSquareIntegrable_coe X).memLp_limitProcess.toLp _) 𝓕 P) t,
      condExp_congr_ae ((isSquareIntegrable_coe X).memLp_limitProcess.coeFn_toLp),
      (isSquareIntegrable_coe X).condExp_limitProcess_ae_eq t] with ω h1 h2 h3 h4
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
    grw [𝓕.limitProcess_congr (mk_ae_eq _)]
    filter_upwards [h1,
      (isSquareIntegrable_modif_condExp 𝓕 (Lp.memLp X.1)).ae_tendsto_limitProcess,
      tendsto_ae_condExp' 𝓕 X.1,
      condExp_of_aestronglyMeasurable' (iSup_le 𝓕.le) X.2
        ((Lp.memLp X.1).integrable (by simp))] with ω h1 h2 h3 h4
    rw [← h4]
    apply tendsto_nhds_unique ?_ (h3.comp hu)
    apply Tendsto.congr h1 (h2.comp hu)
  norm_map' X := rfl

instance SquareIntegrable.completeSpace [OrderTopology ι] :
    CompleteSpace (SquareIntegrable ι E P 𝓕) :=
  haveI : Fact (⨆ t, 𝓕 t ≤ mΩ) := ⟨iSup_le 𝓕.le⟩
  toL2Isom.toIsometryEquiv.completeSpace

variable [OrderTopology ι] [IsFiniteMeasure P]

variable (ι E P 𝓕) in
/-- The set of continuous square integrable martingales, as a submodule of the type of
square-integrable martingales, see `SquareIntegrable`. -/
def continuousSquareIntegrable : Submodule ℝ (SquareIntegrable ι E P 𝓕) where
  carrier := {X | ∃ Y : ι → Ω → E, (∀ ω, Continuous (Y · ω)) ∧ IsSquareIntegrable Y 𝓕 P ∧
      Y ≡ᵐ[P] SquareIntegrable.out X}
  add_mem' := by
    rintro X Y ⟨X', hX1, hX2, hX3⟩ ⟨Y', hY1, hY2, hY3⟩
    refine ⟨X' + Y', fun ω ↦ (hX1 ω).add (hY1 ω), hX2.add hY2, ?_⟩
    filter_upwards [SquareIntegrable.coe_add X Y, hX3, hY3] with ω h1 h2 h3 t
    simp_all
  zero_mem' := by
    refine ⟨0, by fun_prop, sorry, ?_⟩
    filter_upwards [SquareIntegrable.coe_zero E P 𝓕] with ω h t
    rw [h]
  smul_mem' := by
    rintro c X ⟨X', hX1, hX2, hX3⟩
    refine ⟨c • X', fun ω ↦ (hX1 ω).const_smul c, hX2.smul c, ?_⟩
    filter_upwards [SquareIntegrable.coe_smul X c, hX3] with ω h1 h2 t
    simp_all

-- noncomputable def continuousSquareIntegrable.out (X : continuousSquareIntegrable ι E P 𝓕) :
--     ι → Ω → E :=
--   X.2.choose

noncomputable instance : CoeFun (continuousSquareIntegrable ι E P 𝓕) (fun _ ↦ ι → Ω → E) where
  coe X := X.1

lemma continuous_coe (X : continuousSquareIntegrable ι E P 𝓕) :
    ∀ᵐ ω ∂P, Continuous (X · ω) := by
  obtain ⟨Y, hY1, -, hY2⟩ := X.2
  filter_upwards [hY2] with ω h
  apply (hY1 ω).congr h

-- lemma isSquareIntegrable_out (X : continuousSquareIntegrable ι E P 𝓕) :
--     IsSquareIntegrable (continuousSquareIntegrable.out X) 𝓕 P :=
--   X.2.choose_spec.2.1

-- lemma out_ae_eq (X : continuousSquareIntegrable ι E P 𝓕) :
--     (fun ω t ↦ continuousSquareIntegrable.out X t ω) =ᵐ[P] X.1.1 :=
--   X.2.choose_spec.2.2

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
    [IsFiniteMeasure P] [SigmaFiniteFiltration P 𝓕] : ι → Ω → E :=
  if hX : IsAESquareIntegrable X 𝓕 P
    then (continuousSquareIntegrable ι E P 𝓕).orthogonalProjectionOnto (SquareIntegrable.mk X hX)
    else 0

lemma continuousPart_congr {X Y : ι → Ω → E} (hXY : X ≡ᵐ[P] Y) :
    continuousPart X 𝓕 P = continuousPart Y 𝓕 P := by
  by_cases hX : IsAESquareIntegrable X 𝓕 P
  · simp only [continuousPart, hX, ↓reduceDIte, hX.congr hXY]
    ext t ω
    congr 3
    rwa [SquareIntegrable.mk_eq_mk]
  simp [continuousPart, hX, (isAESquareIntegrable_congr hXY).not.1 hX]

lemma continuous_continuousPart (X : ι → Ω → E) :
    ∀ᵐ ω ∂P, Continuous (continuousPart X 𝓕 P · ω) := by
  rw [continuousPart]
  split_ifs
  · exact continuous_coe _
  simp [continuous_const]

lemma isSquareIntegrable_continuousPart {X : ι → Ω → E} :
    IsSquareIntegrable (continuousPart X 𝓕 P) 𝓕 P := by
  rw [continuousPart]
  split_ifs
  · exact SquareIntegrable.isSquareIntegrable_coe _
  · sorry

variable (P 𝓕) in
noncomputable def discontinuousPart (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω)
    [IsFiniteMeasure P] [SigmaFiniteFiltration P 𝓕] : ι → Ω → E :=
  X - continuousPart X 𝓕 P

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
    P[fun ω ↦ ⟪𝓕.limitProcess X P ω, 𝓕.limitProcess Y P ω⟫] = 0

lemma isPurelyDiscontinuous_discontinuousPart [Bot ι] {X : ι → Ω → E}
    (hX : IsAESquareIntegrable X 𝓕 P) :
    IsPurelyDiscontinuous P 𝓕 (discontinuousPart X 𝓕 P) := by
  constructor
  · exact hX.sub isSquareIntegrable_continuousPart.isAESquareIntegrable
  intro Y hY1 hY2

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
