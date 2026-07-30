/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import BrownianMotion.StochasticIntegral.DoobMeyer
public import BrownianMotion.StochasticIntegral.VariationProcess

@[expose] public section

open MeasureTheory Filter Order ProbabilityTheory Convexity
open scoped RealInnerProductSpace

variable {ι Ω : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → ℝ} {𝓕 : Filtration ι mΩ}
  [MeasurableSpace ι] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {X : ι → Ω → E} [CompleteSpace E]

namespace ProbabilityTheory

def predictableStrongDual (X : ι → Ω → E) (t : ι) (ω : Ω) : StrongDual ℝ E where
  toFun x := IsLocalSubmartingale.predictablePart (fun t ω ↦ ⟪X t ω, x⟫) 𝓕 P t ω
  map_add' x y := by simp

end ProbabilityTheory
