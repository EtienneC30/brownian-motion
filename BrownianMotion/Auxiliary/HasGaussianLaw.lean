import BrownianMotion.Gaussian.Gaussian
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Probability.Independence.CharacteristicFunction

open MeasureTheory ProbabilityTheory Finset WithLp Complex
open scoped NNReal

namespace ProbabilityTheory

variable {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}

section charFun

lemma HasGaussianLaw.charFun_toLp_pi {X : ι → Ω → ℝ} [hX : HasGaussianLaw (fun ω ↦ (X · ω)) P]
    (ξ : EuclideanSpace ℝ ι) :
    charFun (P.map (fun ω ↦ toLp 2 (X · ω))) ξ =
      exp (∑ i, ξ i * P[X i] * I - ∑ i, ∑ j, (ξ i : ℂ) * ξ j * (cov[X i, X j; P] / 2)) := by
  have := hX.isProbabilityMeasure
  nth_rw 1 [IsGaussian.charFun_eq, covInnerBilin_apply_pi, EuclideanSpace.real_inner_eq]
  · simp_rw [ofReal_sum, Finset.sum_mul, ← mul_div_assoc, Finset.sum_div,
      integral_complex_ofReal, ← ofReal_mul]
    congrm exp (∑ i, Complex.ofReal (_ * ?_) * I - _)
    rw [integral_map, eval_integral_piLp]
    · simp
    · simp only [id_eq, PiLp.toLp_apply]
      exact fun i ↦ HasGaussianLaw.integrable
    · have := hX.aemeasurable
      fun_prop
    · exact aestronglyMeasurable_id
  · exact fun i ↦ HasGaussianLaw.memLp_two

lemma HasGaussianLaw.charFun_toLp_prodMk {X Y : Ω → ℝ} [hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P]
    (ξ : WithLp 2 (ℝ × ℝ)) :
    charFun (P.map (fun ω ↦ toLp 2 (X ω, Y ω))) ξ =
      exp ((ξ.1 * P[X] + ξ.2 * P[Y]) * I -
        (ξ.1 ^ 2 * Var[X; P] + 2 * ξ.1 * ξ.2 * cov[X, Y; P] + ξ.2 ^ 2 * Var[Y; P]) / 2) := by
  have := hXY.isProbabilityMeasure
  nth_rw 1 [IsGaussian.charFun_eq, covInnerBilin_apply_prod]
  · simp only [id_eq, prod_inner_apply, ofLp_fst, RCLike.inner_apply, conj_trivial, ofLp_snd,
      ofReal_add, ofReal_mul, add_mul, add_div, integral_complex_ofReal, pow_two, mul_comm]
    congrm exp (I * (_ * ?_ + _ * ?_) - ?_)
    · rw [integral_map, fst_integral_withLp]
      · simp
      · exact HasGaussianLaw.integrable
      · fun_prop
      · exact aestronglyMeasurable_id
    · rw [integral_map, snd_integral_withLp]
      · simp
      · exact HasGaussianLaw.integrable
      · fun_prop
      · exact aestronglyMeasurable_id
    · ring
  · exact hXY.fst.memLp_two
  · exact hXY.snd.memLp_two

end charFun

lemma HasGaussianLaw.iIndepFun_of_covariance_eq_zero {X : ι → Ω → ℝ}
    [h1 : HasGaussianLaw (fun ω ↦ (X · ω)) P] (h2 : ∀ i j : ι, i ≠ j → cov[X i, X j; P] = 0) :
    iIndepFun X P := by
  have := h1.isProbabilityMeasure
  refine iIndepFun_iff_charFun_pi h1.aemeasurable.eval |>.2 fun ξ ↦ ?_
  simp_rw [HasGaussianLaw.charFun_toLp_pi, ← sum_sub_distrib, Complex.exp_sum,
    HasGaussianLaw.charFun_map_real]
  congrm ∏ i, Complex.exp (_ - ?_)
  rw [Fintype.sum_eq_single i]
  · simp [covariance_self, h1.aemeasurable.eval, pow_two, mul_div_assoc]
  · exact fun j hj ↦ by simp [h2 i j hj.symm]

lemma HasGaussianLaw.indepFun_of_covariance_eq_zero {X Y : Ω → ℝ}
    [h1 : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P] (h2 : cov[X, Y; P] = 0) :
    IndepFun X Y P := by
  have := h1.isProbabilityMeasure
  refine indepFun_iff_charFun_prod h1.aemeasurable.fst h1.aemeasurable.snd |>.2 fun ξ ↦ ?_
  simp_rw [HasGaussianLaw.charFun_toLp_prodMk, h1.fst.charFun_map_real,
    h1.snd.charFun_map_real, ← Complex.exp_add, h2, Complex.ofReal_zero, mul_zero,
    WithLp.ofLp_fst, WithLp.ofLp_snd]
  congr
  ring

open ContinuousLinearMap in
lemma iIndepFun.hasGaussianLaw {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]
    {X : Π i, Ω → (E i)} (h : ∀ i, HasGaussianLaw (X i) P) (hX : iIndepFun X P) :
    HasGaussianLaw (fun ω ↦ (X · ω)) P where
  isGaussian_map := by
    have := hX.isProbabilityMeasure
    obtain hι | hι := isEmpty_or_nonempty ι
    · have : P.map (fun ω ↦ fun x ↦ X x ω) = .dirac hι.elim := by
        ext s -
        apply Subsingleton.set_cases (p := fun s ↦ Measure.map _ _ s = _)
        · simp
        simp only [measure_univ]
        exact @measure_univ _ _ _ (Measure.isProbabilityMeasure_map (by fun_prop))
      rw [this]
      infer_instance
    classical
    rw [isGaussian_iff_gaussian_charFunDual]
    refine ⟨fun i ↦ ∫ ω, X i ω ∂P, .diagonalStrongDual (fun i ↦ covarianceBilinDual (P.map (X i))),
      ContinuousBilinForm.isPosSemidef_diagonalStrongDual
        (fun i ↦ isPosSemidef_covarianceBilinDual), fun L ↦ ?_⟩
    rw [(iIndepFun_iff_charFunDual_pi _).1 hX]
    · simp only [← sum_single_apply E (fun i ↦ ∫ ω, X i ω ∂P), map_sum, ofReal_sum, sum_mul,
      ContinuousBilinForm.diagonalStrongDual_apply, sum_div, ← sum_sub_distrib, exp_sum]
      congr with i
      rw [IsGaussian.charFunDual_eq, integral_complex_ofReal,
        ContinuousLinearMap.integral_comp_id_comm, covarianceBilinDual_self_eq_variance,
        integral_map]
      · simp
      · exact HasGaussianLaw.aemeasurable
      · exact aestronglyMeasurable_id
      · exact IsGaussian.memLp_two_id
      · exact IsGaussian.integrable_id
    · exact fun i ↦ HasGaussianLaw.aemeasurable

open ContinuousLinearMap in
lemma HasGaussianLaw.iIndepFun_of_cov {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]
    {X : Π i, Ω → (E i)} (h : HasGaussianLaw (fun ω i ↦ X i ω) P)
    (h' : ∀ i j, i ≠ j → ∀ (L₁ : StrongDual ℝ (E i)) (L₂ : StrongDual ℝ (E j)),
      cov[L₁ ∘ (X i), L₂ ∘ (X j); P] = 0) :
    iIndepFun X P := by
  have := h.isProbabilityMeasure
  classical
  rw [iIndepFun_iff_charFunDual_pi]
  · intro L
    simp_rw [IsGaussian.charFunDual_eq]
    rw [← Complex.exp_sum, sum_sub_distrib, ← sum_mul]
    · congr
      · have this ω : L (X · ω) = ∑ i, L (Pi.single i (X i ω)) := by
          rw [← map_sum, sum_single_apply]
        rw [integral_map]
        · simp_rw [this, Complex.ofReal_sum]
          rw [integral_finset_sum]
          · congr with i
            rw [integral_map]
            · rfl
            · exact HasGaussianLaw.aemeasurable
            · fun_prop
          · rintro i -
            apply Integrable.ofReal
            change Integrable (L ∘ (single ℝ E i) ∘ X i) P
            exact HasGaussianLaw.integrable
        · exact h.aemeasurable
        · fun_prop
      · have this : L ∘ (fun ω i ↦ X i ω) = ∑ i, (L ∘L (single ℝ E i)) ∘ (X i) := by
          ext ω
          simp [← map_sum, sum_single_apply]
        rw [variance_map, this, variance_sum]
        · simp only [← sum_div, ← ofReal_sum, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
            div_left_inj', ofReal_inj]
          congr with i
          rw [sum_eq_single_of_mem i (by grind) (fun j _ hij ↦ ?_)]
          · rw [variance_map, covariance_self]
            · exact HasGaussianLaw.aemeasurable
            · fun_prop
            · exact HasGaussianLaw.aemeasurable
          exact h' i j hij.symm _ _
        · exact fun _ ↦ HasGaussianLaw.memLp_two
        · fun_prop
        · exact HasGaussianLaw.aemeasurable
  · exact fun _ ↦ HasGaussianLaw.aemeasurable

lemma test {ι κ : Type*} {𝓧 : ι → Type*} {𝓨 : κ → Type*} [∀ i, MeasurableSpace (𝓧 i)]
    [∀ j, MeasurableSpace (𝓨 j)] {X : (i : ι) → Ω → 𝓧 i} {Y : (j : κ) → Ω → 𝓨 j}
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (h : ∀ (S : Finset ι) (T : Finset κ),
      IndepFun (fun ω (i : S) ↦ X i ω) (fun ω (j : T) ↦ Y j ω) P) [IsProbabilityMeasure P] :
    IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P := by
  let πSβ := MeasureTheory.squareCylinders (fun i ↦ {s : Set (𝓧 i) | MeasurableSet s})
  let πS := { s : Set Ω | ∃ t ∈ πSβ, (fun ω i => X i ω) ⁻¹' t = s }
  have hπS_pi : IsPiSystem πS := by
    refine IsPiSystem.comap (isPiSystem_squareCylinders ?_ ?_) _
    · exact fun i ↦ MeasurableSpace.isPiSystem_measurableSet
    · simp
  have hπS_gen : (MeasurableSpace.pi.comap fun a i => X i a) = .generateFrom πS := by
    rw [generateFrom_squareCylinders.symm, MeasurableSpace.comap_generateFrom]
    congr
  let πTβ := squareCylinders (fun j ↦ {s : Set (𝓨 j) | MeasurableSet s})
  let πT := { s : Set Ω | ∃ t ∈ πTβ, (fun a j => Y j a) ⁻¹' t = s }
  have hπT_pi : IsPiSystem πT := by
    refine IsPiSystem.comap (isPiSystem_squareCylinders ?_ ?_) _
    · exact fun i ↦ MeasurableSpace.isPiSystem_measurableSet
    · simp
  have hπT_gen : (MeasurableSpace.pi.comap fun a j => Y j a) = .generateFrom πT := by
    rw [generateFrom_squareCylinders.symm, MeasurableSpace.comap_generateFrom]
    congr
  -- To prove independence, we prove independence of the generating π-systems.
  refine IndepSets.indep (Measurable.comap_le (measurable_pi_iff.mpr fun i => hX i))
    (Measurable.comap_le (measurable_pi_iff.mpr fun i => hY i)) hπS_pi hπT_pi hπS_gen hπT_gen
    ((IndepSets_iff _ _ _).2 ?_)
  rintro - - ⟨s, ⟨sets_s, hs1, hs2, rfl⟩, rfl⟩ ⟨t, ⟨sets_t, ht1, ht2, rfl⟩, rfl⟩
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_setOf_eq, forall_const] at hs2 ht2
  have : (fun ω i ↦ X i ω) ⁻¹' sets_s.toSet.pi hs1 ∩ (fun a j ↦ Y j a) ⁻¹' sets_t.toSet.pi ht1 =
      (fun ω (i : sets_s) ↦ X i ω) ⁻¹' (Finset.univ).toSet.pi (fun i ↦ hs1 i) ∩
      (fun a (j : sets_t) ↦ Y j a) ⁻¹' Finset.univ.toSet.pi (fun j ↦ ht1 j) := by
    ext; simp
  rw [this, (h sets_s sets_t).meas_inter]
  · congr 2
    · ext; simp
    · ext; simp
  · apply MeasurableSet.preimage
    · exact MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ ↦ hs2 _)
    · exact comap_measurable _
  · apply MeasurableSet.preimage
    · exact MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ ↦ ht2 _)
    · exact comap_measurable _

lemma test' {ι : Type*} {κ : ι → Type*} {𝓧 : (i : ι) → (j : κ i) → Type*}
    [∀ i j, MeasurableSpace (𝓧 i j)] {X : (i : ι) → (j : κ i) → Ω → 𝓧 i j}
    (hX : ∀ i j, Measurable (X i j))
    (h : ∀ (S : Finset ι) (T : (i : S) → Finset (κ i)),
      iIndepFun (fun i ω (j : T i) ↦ X i j ω) P) [IsProbabilityMeasure P] :
    iIndepFun (fun i ω j ↦ X i j ω) P := by
  let πsys (i : ι) := squareCylinders (fun j ↦ {s : Set (𝓧 i j) | MeasurableSet s})
  let πsys' i := {s : Set Ω | ∃ t ∈ πsys i, (fun ω j ↦ X i j ω) ⁻¹' t = s}
  have πsys'_pi i : IsPiSystem (πsys' i) := by
    refine IsPiSystem.comap (isPiSystem_squareCylinders ?_ ?_) _
    · exact fun i ↦ MeasurableSpace.isPiSystem_measurableSet
    · simp
  have πsys'_gen i : (MeasurableSpace.pi.comap fun ω j ↦ X i j ω) = .generateFrom (πsys' i) := by
    rw [generateFrom_squareCylinders.symm, MeasurableSpace.comap_generateFrom]
    congr
  refine iIndepSets.iIndep (fun i ↦ (Measurable.comap_le (measurable_pi_iff.mpr fun j => hX i j)))
    πsys' πsys'_pi πsys'_gen ((iIndepSets_iff _ _).2 ?_)
  intro S f hf
  simp only [squareCylinders, Set.mem_pi, Set.mem_univ, Set.mem_setOf_eq, forall_const,
    ↓existsAndEq, and_true, πsys', πsys] at hf
  choose! T s hs hf using hf
  rw [Set.iInter₂_congr (fun i hi ↦ (hf i hi).symm),
    S.prod_congr rfl (fun i hi ↦ congrArg P (hf i hi).symm)]
  have : (⋂ i ∈ S, (fun ω j ↦ X i j ω) ⁻¹' (T i).toSet.pi (s i)) =
      (⋂ i ∈ (univ : Finset S), (fun ω (j : T i) ↦ X i j ω) ⁻¹' univ.toSet.pi (fun j ↦ s i j)) := by
    ext; simp
  rw [this, (h S (fun i ↦ T i)).measure_inter_preimage_eq_mul, ← S.prod_coe_sort]
  · congrm ∏ _, P ?_
    ext; simp
  · exact fun i _ ↦ .pi (Finset.countable_toSet _) (fun _ _ ↦ hs _ i.2 _)

open ContinuousLinearMap in
lemma HasGaussianLaw.indepFun_of_cov {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [CompleteSpace F] [BorelSpace F] [SecondCountableTopology F]
    {X : Ω → E} {Y : Ω → F} (h : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P)
    (h' : ∀ (L₁ : StrongDual ℝ E) (L₂ : StrongDual ℝ F), cov[L₁ ∘ X, L₂ ∘ Y; P] = 0) :
    IndepFun X Y P := by
  have := h.isProbabilityMeasure
  have := h.fst
  have := h.snd
  rw [indepFun_iff_charFunDual_prod]
  · intro L
    have : L ∘ (fun ω ↦ (X ω, Y ω)) = (L ∘L (.inl ℝ E F)) ∘ X + (L ∘L (.inr ℝ E F)) ∘ Y := by
      ext; simp only [Function.comp_apply, ← comp_inl_add_comp_inr, Pi.add_apply]
    rw [IsGaussian.charFunDual_eq, h.fst.isGaussian_map.charFunDual_eq,
      h.snd.isGaussian_map.charFunDual_eq, ← exp_add, sub_add_sub_comm, ← add_mul, integral_map,
      integral_map, integral_map, integral_complex_ofReal, integral_complex_ofReal,
      integral_complex_ofReal, ← ofReal_add, ← integral_add, ← add_div, ← ofReal_add,
      variance_map, variance_map, variance_map, this, variance_add, h', mul_zero, add_zero]
    · congr
    · exact (h.fst.map _).memLp_two
    · exact (h.snd.map _).memLp_two
    any_goals fun_prop
    all_goals exact HasGaussianLaw.integrable
  all_goals fun_prop

open ContinuousLinearMap RealInnerProductSpace in
lemma HasGaussianLaw.iIndepFun_of_cov' {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]
    {X : Π i, Ω → (E i)} (h : HasGaussianLaw (fun ω i ↦ X i ω) P)
    (h' : ∀ i j, i ≠ j → ∀ (x : E i) (y : E j),
      cov[fun ω ↦ ⟪x, X i ω⟫, fun ω ↦ ⟪y, X j ω⟫; P] = 0) :
    iIndepFun X P := by
  apply h.iIndepFun_of_cov
  intro i j hij L₁ L₂
  simp_rw [← inner_toDual_symm_eq_self]
  exact h' i j hij _ _

open ContinuousLinearMap RealInnerProductSpace in
lemma HasGaussianLaw.indepFun_of_cov' {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
    [CompleteSpace F] [BorelSpace F] [SecondCountableTopology F]
    {X : Ω → E} {Y : Ω → F} (h : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P)
    (h' : ∀ x y, cov[fun ω ↦ ⟪x, X ω⟫, fun ω ↦ ⟪y, Y ω⟫; P] = 0) :
    IndepFun X Y P := by
  apply h.indepFun_of_cov
  intro L₁ L₂
  simp_rw [← inner_toDual_symm_eq_self]
  exact h' _ _

open ContinuousLinearMap RealInnerProductSpace in
lemma HasGaussianLaw.iIndepFun_of_cov'' {κ : ι → Type*} [∀ i, Fintype (κ i)] [DecidableEq ι]
    {X : (i : ι) → κ i → Ω → ℝ} (h : HasGaussianLaw (fun ω i j ↦ X i j ω) P)
    (h' : ∀ i j, i ≠ j → ∀ k l, cov[X i k, X j l; P] = 0) :
    iIndepFun (fun i ω j ↦ X i j ω) P := by
  have := h.isProbabilityMeasure
  have _ i j := (h.eval i).eval j
  have : (fun i ω j ↦ X i j ω) = fun i ↦ (ofLp ∘ (toLp 2 ∘ fun ω j ↦ X i j ω)) := by
    ext; simp
  rw [this]
  apply iIndepFun.comp
  · apply (h.toLp_comp_pi 2).iIndepFun_of_cov'
    intro i j hij x y
    rw [← (EuclideanSpace.basisFun _ _).sum_repr x, ← (EuclideanSpace.basisFun _ _).sum_repr y]
    simp_rw [sum_inner, inner_smul_left]
    rw [covariance_fun_sum_fun_sum]
    · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
        EuclideanSpace.basisFun_inner, PiLp.toLp_apply]
      refine Finset.sum_eq_zero fun k _ ↦ Finset.sum_eq_zero fun l _ ↦ ?_
      rw [covariance_mul_left, covariance_mul_right, h' i j hij k l, mul_zero, mul_zero]
    · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
        EuclideanSpace.basisFun_inner, PiLp.toLp_apply]
      exact fun _ ↦ HasGaussianLaw.memLp_two.const_mul _
    · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
        EuclideanSpace.basisFun_inner, PiLp.toLp_apply]
      exact fun _ ↦ HasGaussianLaw.memLp_two.const_mul _
  · fun_prop

open ContinuousLinearMap RealInnerProductSpace in
lemma HasGaussianLaw.indepFun_of_cov'' {κ : Type*} [Fintype κ]
    {X : ι → Ω → ℝ} {Y : κ → Ω → ℝ} (h : HasGaussianLaw (fun ω ↦ (fun i ↦ X i ω, fun j ↦ Y j ω)) P)
    (h' : ∀ i j, cov[X i, Y j; P] = 0) :
    IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P := by
  have := h.isProbabilityMeasure
  have _ i := h.fst.eval i
  have _ j := h.snd.eval j
  have hX : (fun ω i ↦ X i ω) = (ofLp ∘ (toLp 2 ∘ fun ω i ↦ X i ω)) := by
    ext; simp
  have hY : (fun ω j ↦ Y j ω) = (ofLp ∘ (toLp 2 ∘ fun ω j ↦ Y j ω)) := by
    ext; simp
  rw [hX, hY]
  apply IndepFun.comp
  · apply HasGaussianLaw.indepFun_of_cov'
    · have : (fun ω ↦ ((toLp 2 ∘ fun ω i ↦ X i ω) ω, (toLp 2 ∘ fun ω j ↦ Y j ω) ω)) =
          ((PiLp.continuousLinearEquiv 2 ℝ (fun _ ↦ ℝ)).symm.toContinuousLinearMap.prodMap
            (PiLp.continuousLinearEquiv 2 ℝ (fun _ ↦ ℝ)).symm.toContinuousLinearMap) ∘
            (fun ω ↦ (fun i ↦ X i ω, fun j ↦ Y j ω)) := by
        ext; all_goals simp
      rw [this]
      infer_instance
    intro x y
    rw [← (EuclideanSpace.basisFun _ _).sum_repr x, ← (EuclideanSpace.basisFun _ _).sum_repr y]
    simp_rw [sum_inner, inner_smul_left]
    rw [covariance_fun_sum_fun_sum]
    · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner, PiLp.toLp_apply]
      refine Finset.sum_eq_zero fun k _ ↦ Finset.sum_eq_zero fun l _ ↦ ?_
      rw [covariance_mul_left, covariance_mul_right, h', mul_zero, mul_zero]
    · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner, PiLp.toLp_apply]
      exact fun _ ↦ HasGaussianLaw.memLp_two.const_mul _
    · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
        EuclideanSpace.basisFun_inner, PiLp.toLp_apply]
      exact fun _ ↦ HasGaussianLaw.memLp_two.const_mul _
  · fun_prop
  · fun_prop

variable {X Y : Ω → ℝ} {μX μY : ℝ} {vX vY : ℝ≥0}

lemma IndepFun.hasLaw_sub_of_gaussian
    (hX : HasLaw X (gaussianReal μX vX) P) (hY : HasLaw Y (gaussianReal μY vY) P)
    (h1 : IndepFun X (Y - X) P) (h2 : vX ≤ vY) :
    HasLaw (Y - X) (gaussianReal (μY - μX) (vY - vX)) P where
  map_eq := by
    have : IsProbabilityMeasure P := hX.hasGaussianLaw.isProbabilityMeasure
    refine Measure.ext_of_charFun <| funext fun t ↦ ?_
    apply mul_left_cancel₀ (a := charFun (P.map X) t)
    · rw [hX.map_eq, charFun_gaussianReal]
      exact Complex.exp_ne_zero _
    · rw [← Pi.mul_apply, ← h1.charFun_map_add_eq_mul, add_sub_cancel, hY.map_eq, hX.map_eq,
        charFun_gaussianReal, charFun_gaussianReal, charFun_gaussianReal, ← Complex.exp_add,
        NNReal.coe_sub h2, Complex.ofReal_sub]
      · congr
        field_simp
        push_cast
        ring
      all_goals fun_prop

lemma IndepFun.hasLaw_gaussianReal_of_add
    (hX : HasLaw X (gaussianReal μX vX) P) (hY : HasLaw (X + Y) (gaussianReal μY vY) P)
    (h : IndepFun X Y P) :
    HasLaw Y (gaussianReal (μY - μX) (vY - vX)) P := by
  have h' := h
  rw [show Y = X + Y - X by simp] at h' ⊢
  apply h'.hasLaw_sub_of_gaussian hX hY
  rw [← @Real.toNNReal_coe vY, ← @variance_id_gaussianReal μY vY, ← hY.variance_eq,
    h.variance_add, hX.variance_eq, variance_id_gaussianReal, Real.toNNReal_add,
    Real.toNNReal_coe]
  any_goals simp
  · exact variance_nonneg _ _
  · exact hX.hasGaussianLaw.memLp_two
  · convert hY.hasGaussianLaw.memLp_two.sub hX.hasGaussianLaw.memLp_two
    simp

lemma IndepFun.hasGaussianLaw_of_add_real
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw (X + Y) P) (h : IndepFun X Y P) :
    HasGaussianLaw Y P where
  isGaussian_map := by
    have h1 : HasLaw X (gaussianReal _ _) P := ⟨hX.aemeasurable, hX.map_eq_gaussianReal⟩
    have h2 : HasLaw (X + Y) (gaussianReal _ _) P := ⟨hY.aemeasurable, hY.map_eq_gaussianReal⟩
    have := h.hasLaw_gaussianReal_of_add h1 h2
    exact this.hasGaussianLaw.isGaussian_map

lemma IndepFun.hasGaussianLaw_sub {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {X Y : Ω → E} (hX : HasGaussianLaw X P)
    (hY : HasGaussianLaw Y P) (h : IndepFun X (Y - X) P) :
    HasGaussianLaw (Y - X) P where
  isGaussian_map := by
    refine ⟨fun L ↦ ?_⟩
    conv => enter [2, 1, 2, x]; change id (L x)
    rw [← integral_map, ← variance_id_map]
    · refine @IsGaussian.eq_gaussianReal _ ?_
      rw [AEMeasurable.map_map_of_aemeasurable]
      · refine @HasGaussianLaw.isGaussian_map (self := ?_)
        apply IndepFun.hasGaussianLaw_of_add_real (X := L ∘ X)
        · infer_instance
        · rw [← map_comp_add, add_sub_cancel]
          infer_instance
        · exact h.comp L.measurable L.measurable
      · fun_prop
      · exact hY.aemeasurable.sub hX.aemeasurable
    all_goals fun_prop

end ProbabilityTheory
