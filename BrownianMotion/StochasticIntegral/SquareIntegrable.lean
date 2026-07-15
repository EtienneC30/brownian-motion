/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.Auxiliary.Martingale
public import BrownianMotion.StochasticIntegral.LocalMartingale

/-! # Square integrable martingales

-/

@[expose] public section

open MeasureTheory Filter Function TopologicalSpace
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι] [TopologicalSpace ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ι → Ω → E} {𝓕 : Filtration ι mΩ}

/-- A square integrable martingale is a martingale with cadlag paths and uniformly bounded
second moments. -/
structure IsSquareIntegrable (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) : Prop where
  martingale : Martingale X 𝓕 P
  cadlag : ∀ ω, IsCadlag (X · ω)
  bounded : ⨆ i, eLpNorm (X i) 2 P < ∞

lemma IsSquareIntegrable.const_fun [OrderBot ι] {ξ : Ω → E} (mξ : StronglyMeasurable[𝓕 ⊥] ξ)
    [SigmaFiniteFiltration P 𝓕] (hξ1 : Integrable ξ P) (hξ2 : MemLp ξ 2 P) :
    IsSquareIntegrable (fun _ ↦ ξ) 𝓕 P where
  martingale := martingale_const_fun 𝓕 P mξ hξ1
  cadlag ω := isCadlag_const

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

lemma IsSquareIntegrable.add [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P)
    (hY : IsSquareIntegrable Y 𝓕 P) :
    IsSquareIntegrable (fun i ω ↦ X i ω + Y i ω) 𝓕 P := by
  refine ⟨hX.martingale.add hY.martingale, fun ω ↦ (hX.2 ω).add (hY.2 ω), ?_⟩
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

lemma IsSquareIntegrable.smul [CompleteSpace E] (hX : IsSquareIntegrable X 𝓕 P) (r : ℝ) :
    IsSquareIntegrable (fun i ω ↦ r • X i ω) 𝓕 P where
  martingale := hX.martingale.smul r
  cadlag ω := by
    simpa [Pi.smul_apply] using (hX.cadlag ω).fun_const_smul r
  bounded := by
    change (⨆ i, eLpNorm (r • X i) 2 P) < ∞
    simp only [eLpNorm_const_smul, ← ENNReal.mul_iSup]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hX.bounded

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

lemma IsSquareIntegrable.tendsto_eLpNorm_two_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    Tendsto (fun i ↦ eLpNorm (X i - 𝓕.limitProcess X P) 2 P) atTop (𝓝 0) := by
  sorry

lemma IsSquareIntegrable.iSup_eLpNorm_eq_eLpNorm_limitProcess (hX : IsSquareIntegrable X 𝓕 P) :
    ⨆ i, eLpNorm (X i) 2 P = eLpNorm (𝓕.limitProcess X P) 2 P := by
  sorry

section Hilbert

variable (ι E P 𝓕) in
/-- The type of square integrable martingales. -/
def SquareIntegrable : Type _ :=
  {X : Ω →ₘ[P] (ι → E) // ∃ Y : ι → Ω → E, IsSquareIntegrable Y 𝓕 P ∧ (fun ω t ↦ Y t ω) =ᵐ[P] X}

instance : NormedAddCommGroup (SquareIntegrable ι E P 𝓕) := sorry

instance : InnerProductSpace ℝ (SquareIntegrable ι E P 𝓕) := sorry

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

variable (ι E P 𝓕) in
/-- The set of continuous square integrable martingales, as a submodule of the type of
square-integrable martingales, see `SquareIntegrable`. -/
def ContinuousSquareIntegrable : Submodule ℝ (SquareIntegrable ι E P 𝓕) where
  carrier := {X | ∃ Y : ι → Ω → E, (∀ ω, Continuous (Y · ω)) ∧ (fun ω t ↦ Y t ω) =ᵐ[P] X.1}
  add_mem' := by
    rintro X Y ⟨X', hX1, hX2⟩ ⟨Y', hY1, hY2⟩
    refine ⟨X' + Y', fun ω ↦ (hX1 ω).add (hY1 ω), ?_⟩
    grw [SquareIntegrable.coe_add, AEEqFun.coeFn_add, ← hX2, ← hY2]
    rfl
  zero_mem' := by
    refine ⟨0, by fun_prop, ?_⟩
    grw [SquareIntegrable.coe_zero, AEEqFun.coeFn_zero]
    rfl
  smul_mem' := by
    rintro c X ⟨X', hX1, hX2⟩
    refine ⟨c • X', fun ω ↦ (hX1 ω).const_smul c, ?_⟩
    grw [SquareIntegrable.coe_smul, AEEqFun.coeFn_smul, ← hX2]
    rfl

instance : IsClosed (ContinuousSquareIntegrable ι E P 𝓕 : Set (SquareIntegrable ι E P 𝓕)) := by
  sorry

open scoped Classical in
/-- The continuous martingale part of a square-integrable martingale.

TODO: we rely on the already existing `AEEqFun` machinery, but this is about equivalence classes
of strongly measurable functions, while here we are interested in undistinguishability only
so measurablility is the way to go. It seems we will need to duplicate `AEEqFun` for the measurable
case. -/
noncomputable def continuousPart [Bot ι] (X : ι → Ω → E) : ι → Ω → E :=
  if hX : IsSquareIntegrable X 𝓕 P
    then fun t ω ↦ ((ContinuousSquareIntegrable ι E P 𝓕).orthogonalProjectionOnto
      ⟨.mk (fun ω t ↦ X t ω) sorry, ⟨(X · - X ⊥), hX.sub, (AEEqFun.coeFn_mk _ _).symm⟩⟩).1.1 ω t - X ⊥ ω
    else 0

end Hilbert

end ProbabilityTheory
