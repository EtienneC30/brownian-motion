/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import BrownianMotion.Auxiliary.HasGaussianLaw
import BrownianMotion.Gaussian.StochasticProcesses
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Gaussian processes

-/

open MeasureTheory

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : T → Ω → E}

section Basic

variable [MeasurableSpace E] [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

/-- A stochastic process is a Gaussian process if all its finite dimensional distributions are
Gaussian. -/
class IsGaussianProcess (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop where
  hasGaussianLaw : ∀ I : Finset T, HasGaussianLaw (fun ω ↦ I.restrict (X · ω)) P

attribute [instance] IsGaussianProcess.hasGaussianLaw

lemma IsGaussianProcess.isProbabilityMeasure [hX : IsGaussianProcess X P] :
    IsProbabilityMeasure P :=
  hX.hasGaussianLaw Classical.ofNonempty |>.isProbabilityMeasure

lemma IsGaussianProcess.aemeasurable [hX : IsGaussianProcess X P] (t : T) :
    AEMeasurable (X t) P := by
  by_contra h
  have := (hX.hasGaussianLaw {t}).isGaussian_map
  rw [Measure.map_of_not_aemeasurable] at this
  · exact this.toIsProbabilityMeasure.ne_zero _ rfl
  · rw [aemeasurable_pi_iff]
    push_neg
    exact ⟨⟨t, by simp⟩, h⟩

lemma IsGaussianProcess.modification [IsGaussianProcess X P] (hXY : ∀ t, X t =ᵐ[P] Y t) :
    IsGaussianProcess Y P where
  hasGaussianLaw I := by
    constructor
    rw [map_restrict_eq_of_forall_ae_eq fun t ↦ (hXY t).symm]
    infer_instance

end Basic

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

instance {E ι : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [Subsingleton ι] :
    BorelSpace (ι → E) := by
  refine ⟨le_antisymm pi_le_borel_pi ?_⟩
  obtain h | h := isEmpty_or_nonempty ι
  · exact fun s _ ↦ Subsingleton.set_cases .empty .univ s
  have := @Unique.mk' ι ⟨Classical.choice h⟩ inferInstance
  rw [borel]
  refine MeasurableSpace.generateFrom_le fun s hs ↦ ?_
  simp only [Pi.topologicalSpace, ciInf_unique, isOpen_induced_eq, Set.mem_image,
    Set.mem_setOf_eq] at hs
  simp_rw [MeasurableSpace.measurableSet_iSup, MeasurableSpace.measurableSet_comap]
  refine MeasurableSpace.GenerateMeasurable.basic _ ⟨Classical.choice h, ?_⟩
  obtain ⟨t, ht, rfl⟩ := hs
  exact ⟨t, ht.measurableSet, by rw [Subsingleton.elim (Classical.choice h) default]⟩

instance IsGaussianProcess.hasGaussianLaw_eval [IsGaussianProcess X P] (t : T) :
    HasGaussianLaw (X t) P := by
  have : X t = (ContinuousLinearMap.proj (R := ℝ) ⟨t, by simp⟩) ∘
    (fun ω ↦ ({t} : Finset T).restrict (X · ω)) := by ext; simp
  rw [this]
  infer_instance

instance IsGaussianProcess.hasGaussianLaw_sub [SecondCountableTopology E] [IsGaussianProcess X P]
    {s t : T} : HasGaussianLaw (X s - X t) P := by
  classical
  have : X s - X t =
      (ContinuousLinearMap.proj (R := ℝ) (ι := ({s, t} : Finset T))
        (φ := fun _ ↦ E) ⟨s, by simp⟩ -
      ContinuousLinearMap.proj (R := ℝ) (ι := ({s, t} : Finset T))
        (φ := fun _ ↦ E) ⟨t, by simp⟩) ∘
    (fun ω ↦ Finset.restrict {s, t} (X · ω)) := by ext; simp
  rw [this]
  infer_instance

instance IsGaussianProcess.hasGaussianLaw_fun_sub [SecondCountableTopology E]
    [IsGaussianProcess X P] {s t : T} : HasGaussianLaw (fun ω ↦ X s ω - X t ω) P :=
  IsGaussianProcess.hasGaussianLaw_sub

instance IsGaussianProcess.hasGaussianLaw_increments [SecondCountableTopology E]
    [IsGaussianProcess X P] {n : ℕ} {t : Fin (n + 1) → T} :
    HasGaussianLaw (fun ω (i : Fin n) ↦ X (t i.succ) ω - X (t i.castSucc) ω) P := by
  classical
  let L : ((Finset.univ.image t) → E) →L[ℝ] Fin n → E :=
    { toFun x i := x ⟨t i.succ, by simp⟩ - x ⟨t i.castSucc, by simp⟩
      map_add' x y := by ext; simp; abel
      map_smul' m x := by ext; simp; module
      cont := by fun_prop }
  have : (fun ω i ↦ X (t i.succ) ω - X (t i.castSucc) ω) =
      L ∘ fun ω ↦ (Finset.univ.image t).restrict (X · ω) := by ext; simp [L]
  rw [this]
  infer_instance

lemma IsGaussianProcess.comp_right [SecondCountableTopology E] {S : Type*} [IsGaussianProcess X P]
    (f : S → T) : IsGaussianProcess (X ∘ f) P where
  hasGaussianLaw I := by
    classical
    let L : ((I.image f) → E) →L[ℝ] (I → E) :=
      { toFun x s := x ⟨f s, Finset.mem_image.2 ⟨s.1, s.2, rfl⟩⟩
        map_add' x y := by ext; simp
        map_smul' c x := by ext; simp }
    have : (fun ω ↦ I.restrict ((X ∘ f) · ω)) = L ∘ (fun ω ↦ (I.image f).restrict (X · ω)) := by
      ext; simp [L]
    rw [this]
    infer_instance

lemma IsGaussianProcess.comp_left [SecondCountableTopology E] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] (L : T → E →L[ℝ] F) [IsGaussianProcess X P] :
    IsGaussianProcess (fun t ω ↦ L t (X t ω)) P where
  hasGaussianLaw I := by
    let L' : (I → E) →L[ℝ] (I → F) :=
      { toFun x t := L t (x t)
        map_add' x y := by ext; simp
        map_smul' c x := by ext; simp }
    have : (fun ω ↦ I.restrict (fun t ↦ L t (X t ω))) =
        L' ∘ (fun ω ↦ I.restrict (X · ω)) := by
      ext; simp [L']
    rw [this]
    infer_instance

instance IsGaussianProcess.smul [SecondCountableTopology E] (c : T → ℝ) [IsGaussianProcess X P] :
    IsGaussianProcess (fun t ω ↦ c t • (X t ω)) P :=
  letI L t : E →L[ℝ] E :=
    { toFun x := c t • x
      map_add' := by simp
      map_smul' := by simp [smul_smul, mul_comm]
      cont := by fun_prop }
  IsGaussianProcess.comp_left L

lemma IsGaussianProcess.indepFun [SecondCountableTopology E] [CompleteSpace E]
    {S T : Type*} {X : S → Ω → E}
    {Y : T → Ω → E}
    (h : IsGaussianProcess (Sum.elim X Y) P) (hX : ∀ s, Measurable (X s))
    (hY : ∀ t, Measurable (Y t))
    (h' : ∀ s t (L₁ L₂ : StrongDual ℝ E), cov[L₁ ∘ X s, L₂ ∘ Y t; P] = 0) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P := by
  have := h.isProbabilityMeasure
  have _ s : HasGaussianLaw (X s) P := h.hasGaussianLaw_eval (.inl s)
  have _ t : HasGaussianLaw (Y t) P := h.hasGaussianLaw_eval (.inr t)
  refine test hX hY fun I J ↦ ?_
  apply HasGaussianLaw.indepFun_of_cov
  · let L : (I.disjSum J → E) →L[ℝ] (I → E) × (J → E) :=
      { toFun x := (fun s ↦ x ⟨Sum.inl s, Finset.inl_mem_disjSum.2 s.2⟩,
          fun t ↦ x ⟨Sum.inr t, Finset.inr_mem_disjSum.2 t.2⟩)
        map_add' x y := by ext <;> simp
        map_smul' c x := by ext <;> simp }
    have : (fun ω ↦ (fun i : I ↦ X i ω, fun j : J ↦ Y j ω)) =
        L ∘ (fun ω ↦ (I.disjSum J).restrict (Sum.elim X Y · ω)) := by
      ext <;> simp [L]
    rw [this]
    infer_instance
  intro L₁ L₂
  classical
  have h1 : L₁ ∘ (fun ω i ↦ X i ω) = ∑ i : I, (L₁ ∘L .single ℝ _ i) ∘ X i := by
    ext ω
    simp only [Function.comp_apply, ← L₁.sum_comp_single, Finset.univ_eq_attach, Finset.sum_apply]
  have h2 : L₂ ∘ (fun ω j ↦ Y j ω) = ∑ j : J, (L₂ ∘L .single ℝ _ j) ∘ Y j := by
    ext ω
    simp only [Function.comp_apply, ← L₂.sum_comp_single, Finset.univ_eq_attach, Finset.sum_apply]
  rw [h1, h2, covariance_sum_sum]
  · exact Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ h' ..
  all_goals exact fun _ ↦ HasGaussianLaw.memLp_two

open RealInnerProductSpace in
lemma IsGaussianProcess.indepFun'
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]
    {S T : Type*} {X : S → Ω → E}
    {Y : T → Ω → E}
    (h : IsGaussianProcess (Sum.elim X Y) P) (hX : ∀ s, Measurable (X s))
    (hY : ∀ t, Measurable (Y t))
    (h' : ∀ s t x y, cov[fun ω ↦ ⟪x, X s ω⟫, fun ω ↦ ⟪y, Y t ω⟫; P] = 0) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P := by
  apply h.indepFun hX hY
  intro s t L₁ L₂
  simp_rw [← inner_toDual_symm_eq_self]
  exact h' ..

open RealInnerProductSpace in
lemma IsGaussianProcess.indepFun''
    {S T : Type*} {X : S → Ω → ℝ}
    {Y : T → Ω → ℝ}
    (h : IsGaussianProcess (Sum.elim X Y) P) (hX : ∀ s, Measurable (X s))
    (hY : ∀ t, Measurable (Y t))
    (h' : ∀ s t, cov[X s, Y t; P] = 0) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P := by
  apply h.indepFun' hX hY
  intro s t x y
  simp [mul_comm, covariance_mul_left, covariance_mul_right, h']

instance IsGaussianProcess.shift [SecondCountableTopology E]
    [Add T] [IsGaussianProcess X P] (t₀ : T) :
    IsGaussianProcess (fun t ω ↦ X (t₀ + t) ω - X t₀ ω) P where
  hasGaussianLaw I := by
    classical
    let L : (({t₀} ∪ I.image (t₀ + ·) : Finset T) → E) →L[ℝ] I → E :=
      { toFun x t := x ⟨t₀ + t.1, Finset.mem_union.2
          (Or.inr (Finset.mem_image.2 ⟨t.1, t.2, rfl⟩))⟩ - x ⟨t₀, by simp⟩
        map_add' x y := by ext; simp; abel
        map_smul' c x := by ext; simp; module }
    have : (fun ω ↦ I.restrict (fun t ↦ X (t₀ + t) ω - X t₀ ω)) =
        L ∘ (fun ω ↦ ({t₀} ∪ I.image (t₀ + ·)).restrict (X · ω)) := by ext; simp [L]
    rw [this]
    infer_instance

instance IsGaussianProcess.restrict [SecondCountableTopology E]
    [IsGaussianProcess X P] (s : Set T) :
    IsGaussianProcess (fun t : s ↦ X t) P where
  hasGaussianLaw I := by
    classical
    let L : (I.image ((↑) : s → T) → E) →L[ℝ] I → E :=
      { toFun x i := x ⟨i.1.1, by simp⟩
        map_add' x y := by ext; simp
        map_smul' c x := by ext; simp }
    have : (fun ω ↦ I.restrict (X · ω)) =
        L ∘ (fun ω ↦ (I.image ((↑) : s → T)).restrict (X · ω)) := by
      ext; simp [L]
    rw [this]
    infer_instance

lemma IsGaussianProcess.obv [SecondCountableTopology E] [IsGaussianProcess X P]
    {S : Type*} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] [SecondCountableTopology F] [CompleteSpace F] {Y : S → Ω → F}
    (h : ∀ s, ∃ I : Finset T, ∃ L : (I → E) →L[ℝ] F, ∀ ω, Y s ω = L (I.restrict (X · ω))) :
    IsGaussianProcess Y P where
  hasGaussianLaw I := by
    choose J L hL using h
    classical
    let K : (I.biUnion J → E) →L[ℝ] I → F :=
      { toFun x s := L s (fun t ↦ x ⟨t.1, Finset.mem_biUnion.2 ⟨s.1, s.2, t.2⟩⟩)
        map_add' x y := by ext; simp [← Pi.add_def]
        map_smul' c x := by ext; simp [← Pi.smul_def]
        cont := by fun_prop }
    have : (fun ω ↦ I.restrict (Y · ω)) = K ∘ (fun ω ↦ (I.biUnion J).restrict (X · ω)) := by
      ext; simp [K, hL]; rfl
    rw [this]
    infer_instance

end ProbabilityTheory
