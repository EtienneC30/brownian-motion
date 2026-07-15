/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import BrownianMotion.StochasticIntegral.DoobMeyer
public import BrownianMotion.StochasticIntegral.SquareIntegrable

/-! # Quadratic variation of locally square-integrable martingales

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  [MeasurableSpace ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}

/-- The quadratic variation of a locally square-integrable martingale, defined as the predictable
part of the Doob-Meyer decomposition of its squared norm. -/
noncomputable
def quadraticVariation [SigmaFiniteFiltration P 𝓕]
    (hX_sq : IsLocallySquareIntegrable X 𝓕 P)
    (hX_cadlag : ∀ ω, IsCadlag (X · ω)) :
    ι → Ω → ℝ :=
  have hX2_cadlag : ∀ ω, IsCadlag (fun t ↦ ‖X t ω‖ ^ 2) :=
    fun ω ↦ IsCadlag.norm_sq (hX_cadlag ω)
  (hX_sq.isLocalSubmartingale_sq_norm).predictablePart
    (fun t ω ↦ ‖X t ω‖ ^ 2) hX2_cadlag

section Increments

variable {ι Ω E : Type*} [TopologicalSpace E] [LinearOrder ι]

/-- The jump of `f` at time `t`. -/
noncomputable def jump [Sub E] (f : ι → E) (t : ι) : E :=
  f t - f.leftLim t

/-- The set of left jump times of the function `f` before time `t`. -/
def leftJumpSetLe (f : ι → E) (t : ι) : Set ι :=
  (leftJumpSet f) ∩ Set.Iic t

/-- The jump part of a function. -/
noncomputable def jumpPart [AddCommGroup E] (f : ι → E) (t : ι) : E :=
  ∑' s : leftJumpSetLe f t, jump f s

end Increments


def continuousPart

end ProbabilityTheory
