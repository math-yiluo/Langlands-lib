/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.WeilSheaf.Finiteness
public import WeilConjectures.WeilSheaf.OpenClosedTriangle
public import WeilConjectures.ZetaFunction.WeilObjectComparisonLocal

/-!
# Open–closed dévissage for the comparison of Weil complexes with Weil objects

Let `j : U ↪ X` be an open immersion and `i : Z ↪ X` a closed immersion onto the complement, of
separated `k₀`-schemes of finite type. For a Weil complex `K` on `X₀`:

* the Grothendieck–Lefschetz formula for `j^*K` and `i^*K` gives it for `K`
  (`AlgebraicGeometry.WeilComplex.SatisfiesLefschetz.of_openClosed`): on the cohomological side by
  the open–closed triangle `Ra_{U!} j^*K → Ra_{X!} K → Ra_{Z!} i^*K →`, on the side of the points
  since every rational point of `X` lies in exactly one of `U` and `Z`;
* local comparisons for `j^*K` and `i^*K` give one for `K`
  (`AlgebraicGeometry.WeilComplex.HasLocalWeilObjectComparison.of_openClosed`), through the direct
  sum of the Weil lower shriek images along `j` and `i`, whose local traces are computed by the
  sheaf–function compatibility `ProEtale.CondensedRing.weilShriekTraceFunction`;
* hence comparisons for `j^*K` and `i^*K` give one for `K`
  (`AlgebraicGeometry.WeilComplex.HasWeilObjectComparison.of_openClosed`).

## Main results

- `AlgebraicGeometry.WeilComplex.finsum_trace_cohomologyFrobeniusModule_eq_add_of_distTriang`:
  additivity of the alternating Frobenius traces of `Hⁱ(Spec k̄, -)` along a distinguished
  triangle of Weil complexes on `Spec k₀`.
- `AlgebraicGeometry.Scheme.Hom.finsum_fieldPoints_eq_add_of_openClosed`: a sum over the rational
  points of `X` splits into the sums over the rational points of `U` and of `Z`.
- `AlgebraicGeometry.WeilComplex.SatisfiesLefschetz.of_openClosed`,
  `AlgebraicGeometry.WeilComplex.HasLocalWeilObjectComparison.of_openClosed`,
  `AlgebraicGeometry.WeilComplex.HasWeilObjectComparison.of_openClosed`, and their versions for
  Weil sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated MonoidalCategory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

attribute [local instance] fact_ringChar_prime_of_finite
  ProEtale.CondensedRing.fintypeFrobeniusFixedPoints

/-! ### Rational points of an open subscheme and of its closed complement -/

section FieldPoints

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] {K : Type u} [Field K] [Algebra k₀ K]

omit [Finite k₀] in
/-- A monomorphism of `k₀`-schemes is injective on rational points. -/
theorem Scheme.Hom.mapFieldPoints_injective (φ : Y ⟶ X) [Mono φ]
    [φ.IsOver (Spec (CommRingCat.of k₀))] :
    Function.Injective (φ.mapFieldPoints (k₀ := k₀) K) :=
  fun _ _ h ↦ Subtype.ext ((cancel_mono φ).1 (congrArg Subtype.val h))

omit [Finite k₀] in
/-- The range of a morphism from the spectrum of a field is the image of its closed point. -/
lemma Scheme.range_eq_singleton_closedPoint (y : Spec (.of K) ⟶ X) :
    Set.range y.base = {y.base (IsLocalRing.closedPoint K)} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, rfl⟩, ?_⟩
  rintro _ ⟨a, rfl⟩
  rw [Subsingleton.elim a (IsLocalRing.closedPoint K)]

omit [Finite k₀] in
/-- A rational point of `X` comes from the open subscheme `j : U ↪ X` if and only if its image
point lies in `U`. -/
theorem Scheme.Hom.mem_range_mapFieldPoints_iff_of_isOpenImmersion (j : Y ⟶ X)
    [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints K) :
    y ∈ Set.range (j.mapFieldPoints K) ↔
      y.1.base (IsLocalRing.closedPoint K) ∈ Set.range j.base := by
  refine ⟨fun ⟨u, hu⟩ ↦ ⟨u.1.base (IsLocalRing.closedPoint K), ?_⟩, fun h ↦ ?_⟩
  · rw [← hu]
    rfl
  · have hsub : Set.range y.1.base ⊆ Set.range j.base := by
      rw [Scheme.range_eq_singleton_closedPoint]
      exact Set.singleton_subset_iff.2 h
    refine ⟨⟨IsOpenImmersion.lift j y.1 hsub, ?_⟩, Subtype.ext (IsOpenImmersion.lift_fac _ _ _)⟩
    rw [← comp_over j (Spec (CommRingCat.of k₀)), ← Category.assoc, IsOpenImmersion.lift_fac,
      y.2]

omit [Finite k₀] in
/-- A rational point of `X` comes from the closed subscheme `i : Z ↪ X` if and only if its image
point lies in `Z`: the spectrum of a field is reduced. -/
theorem Scheme.Hom.mem_range_mapFieldPoints_iff_of_isClosedImmersion (i : Y ⟶ X)
    [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints K) :
    y ∈ Set.range (i.mapFieldPoints K) ↔
      y.1.base (IsLocalRing.closedPoint K) ∈ Set.range i.base := by
  refine ⟨fun ⟨u, hu⟩ ↦ ⟨u.1.base (IsLocalRing.closedPoint K), ?_⟩, fun h ↦ ?_⟩
  · rw [← hu]
    rfl
  · have hsub : i.ker ≤ y.1.ker := by
      rw [Scheme.IdealSheafData.le_ker_iff_range_subset_support, Scheme.Hom.support_ker,
        i.isClosedEmbedding.isClosed_range.closure_eq]
      rintro _ ⟨a, rfl⟩
      rw [Subsingleton.elim a (IsLocalRing.closedPoint K)]
      exact h
    refine ⟨⟨IsClosedImmersion.lift i y.1 hsub, ?_⟩,
      Subtype.ext (IsClosedImmersion.lift_fac _ _ _)⟩
    rw [← comp_over i (Spec (CommRingCat.of k₀)), ← Category.assoc, IsClosedImmersion.lift_fac,
      y.2]

variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))]
  (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]

omit [Finite k₀] in
/-- For a closed immersion `i : Z ↪ X` onto the complement of an open immersion `j : U ↪ X`, a
rational point of `X` comes from `Z` if and only if it does not come from `U`. -/
theorem Scheme.Hom.mem_range_mapFieldPoints_iff_not_of_openClosed
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints K) :
    y ∈ Set.range (i.mapFieldPoints K) ↔ y ∉ Set.range (j.mapFieldPoints K) := by
  rw [i.mem_range_mapFieldPoints_iff_of_isClosedImmersion,
    j.mem_range_mapFieldPoints_iff_of_isOpenImmersion, hij, Set.mem_compl_iff]

omit [Finite k₀] in
/-- **The rational points of `X` split into those of `U` and of `Z`.** For an open immersion
`j : U ↪ X` and a closed immersion `i : Z ↪ X` onto its complement, a sum over the finitely many
rational points of `X` is the sum of the sums over the rational points of `U` and of `Z`. -/
theorem Scheme.Hom.finsum_fieldPoints_eq_add_of_openClosed
    (hij : Set.range i.base = (Set.range j.base)ᶜ) {M : Type*} [AddCommMonoid M]
    [Finite ((X ↘ Spec (CommRingCat.of k₀)).fieldPoints K)]
    (f : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints K → M) :
    ∑ᶠ y, f y = ∑ᶠ u, f (j.mapFieldPoints K u) + ∑ᶠ z, f (i.mapFieldPoints K z) := by
  have hunion : Set.range (j.mapFieldPoints K) ∪ Set.range (i.mapFieldPoints K) = Set.univ :=
    Set.eq_univ_of_forall fun y ↦ by
      rw [Set.mem_union, mem_range_mapFieldPoints_iff_not_of_openClosed (k₀ := k₀) j i hij]
      exact em _
  have hdisj : Disjoint (Set.range (j.mapFieldPoints K)) (Set.range (i.mapFieldPoints K)) :=
    Set.disjoint_left.2 fun y hj hi ↦
      (mem_range_mapFieldPoints_iff_not_of_openClosed (k₀ := k₀) j i hij y).1 hi hj
  rw [← finsum_mem_range (Scheme.Hom.mapFieldPoints_injective (k₀ := k₀) (K := K) j),
    ← finsum_mem_range (Scheme.Hom.mapFieldPoints_injective (k₀ := k₀) (K := K) i),
    ← finsum_mem_union hdisj (Set.toFinite _) (Set.toFinite _), hunion, finsum_mem_univ]

end FieldPoints

/-! ### Additivity of the cohomology of Weil complexes on `Spec k₀` -/

namespace WeilComplex

/-- The cohomology `Hʳ(Spec k̄, M)` of a Weil complex on `Spec k₀` vanishes outside a finite set
of degrees. -/
theorem exists_finset_subsingleton_cohomologyFrobeniusModule
    (M : WeilComplex k₀ l (Spec (CommRingCat.of k₀))) :
    ∃ s : Finset ℤ, ∀ r ∉ s, Subsingleton (M.cohomologyFrobeniusModule r).carrier := by
  obtain ⟨a, b, h⟩ := exists_subsingleton_cohomologyFrobeniusModule M
  refine ⟨Finset.Icc a b, fun r hr ↦ h r ?_⟩
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hr
  exact hr

/-- **Additivity of the alternating Frobenius traces on `Spec k₀`.** For a distinguished triangle
`M₁ → M₂ → M₃ → M₁[1]` of Weil complexes on `Spec k₀`, the alternating sum of the traces of `Fᵐ`
on `Hⁱ(Spec k̄, -)` is additive, by the long exact cohomology sequence. -/
theorem finsum_trace_cohomologyFrobeniusModule_eq_add_of_distTriang
    (T : Triangle (WeilComplex k₀ l (Spec (CommRingCat.of k₀)))) (hT : T ∈ distTriang _)
    (m : ℕ) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        ((T.obj₂.cohomologyFrobeniusModule i).frobeniusEnd ^ m) =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
          ((T.obj₁.cohomologyFrobeniusModule i).frobeniusEnd ^ m) +
        ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
          ((T.obj₃.cohomologyFrobeniusModule i).frobeniusEnd ^ m) := by
  obtain ⟨s₁, h₁⟩ := exists_finset_subsingleton_cohomologyFrobeniusModule T.obj₁
  obtain ⟨s₂, h₂⟩ := exists_finset_subsingleton_cohomologyFrobeniusModule T.obj₂
  obtain ⟨s₃, h₃⟩ := exists_finset_subsingleton_cohomologyFrobeniusModule T.obj₃
  exact LinearMap.finsum_negOnePow_smul_trace_eq_add_of_exact
    (fun i ↦ (T.obj₁.cohomologyFrobeniusModule i).carrier)
    (fun i ↦ (T.obj₂.cohomologyFrobeniusModule i).carrier)
    (fun i ↦ (T.obj₃.cohomologyFrobeniusModule i).carrier)
    (fun i ↦ cohomologyMap T.mor₁ i)
    (fun i ↦ cohomologyMap T.mor₂ i)
    (cohomologyδ T)
    (fun i ↦ exact_cohomologyMap T i hT)
    (fun i i' h ↦ exact_cohomologyδ_left T i i' h hT)
    (fun i i' h ↦ exact_cohomologyδ_right T i i' h hT)
    _ _ _
    (fun i ↦ FrobeniusModule.frobeniusEnd_pow_comp _ (cohomologyMap_frobenius T.mor₁ i) m)
    (fun i ↦ FrobeniusModule.frobeniusEnd_pow_comp _ (cohomologyMap_frobenius T.mor₂ i) m)
    (fun i i' h ↦ FrobeniusModule.frobeniusEnd_pow_comp _ (cohomologyδ_frobenius T i i' h) m)
    (s₁ ∪ s₂ ∪ s₃)
    (fun i hi ↦ h₁ i fun h ↦ hi (by simp [h]))
    (fun i hi ↦ h₂ i fun h ↦ hi (by simp [h]))
    (fun i hi ↦ h₃ i fun h ↦ hi (by simp [h]))

/-! ### The Weil lower shriek along a monomorphism -/

open ProEtale.CondensedRing

section LowerShriek

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

/-- A morphism `φ : Y ⟶ X` of `k₀`-schemes as a morphism `overSpec Y ⟶ overSpec X` of
`Over (Spec k₀)`. -/
noncomputable abbrev overSpecHom (φ : Y ⟶ X) [φ.IsOver (Spec (CommRingCat.of k₀))] :
    overSpec (k₀ := k₀) Y ⟶ overSpec X :=
  Over.homMk φ (comp_over φ _)

omit [Finite k₀] in
/-- A morphism of `k₀`-schemes commutes with the identity automorphisms. -/
lemma refl_hom_comp_overSpecHom (φ : Y ⟶ X) [φ.IsOver (Spec (CommRingCat.of k₀))] :
    (Iso.refl (overSpec (k₀ := k₀) Y)).hom ≫ overSpecHom φ =
      overSpecHom φ ≫ (Iso.refl (overSpec X)).hom := by
  rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- The points of degree `n + 1` for the identity of `Y` lying over the point of an
`𝔽_{q^{n+1}}`-rational point `y` of `X`, along a morphism `φ : Y ⟶ X` of `k₀`-schemes, are the
rational points of `Y` with image `y`. -/
noncomputable def fiberMapFieldPointsEquiv (φ : Y ⟶ X) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1))) :
    {u // φ.mapFieldPoints _ u = y} ≃
      {x : frobeniusFixedPoints (Iso.refl (overSpec (k₀ := k₀) Y)) (n + 1) //
        x.1 ≫ (overSpecHom φ).left =
          (frobeniusFixedPointsReflOfFieldPoint (X := overSpec X) n y).1} :=
  (fieldPointsEquivFrobeniusFixedPointsRefl (X := overSpec (k₀ := k₀) Y) n).subtypeEquiv fun u ↦
    ⟨fun h ↦ by
      subst h
      exact Category.assoc _ _ _,
    fun h ↦ Subtype.ext ((cancel_epi (Spec.map (CommRingCat.ofHom
      (FiniteField.galoisExtension.liftAlgebraicClosure k₀ (n + 1)).toRingHom))).1
        ((Category.assoc _ _ _).symm.trans h))⟩

variable [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

/-- The local trace of the Weil lower shriek `φ_! K'` along a morphism `φ : Y ⟶ X` of
`k₀`-schemes, for the identity automorphisms, at an `𝔽_{q^{n+1}}`-rational point `y` of `X` is
the sum of the local traces of `K'` at the rational points of `Y` over `y`
(`ProEtale.CondensedRing.weilShriekTraceFunction`). -/
theorem weilStalkTraceAlternatingSum_weilLowerShriek_overSpecHom (φ : Y ⟶ X)
    [φ.IsOver (Spec (CommRingCat.of k₀))]
    (K' : WeilBoundedConstructible l (Iso.refl (overSpec (k₀ := k₀) Y)).hom) (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1))) :
    weilStalkTraceAlternatingSum l (n + 1) _
        (frobeniusFixedPointsReflOfFieldPoint (X := overSpec X) n y).2.2
        ((weilLowerShriek l (Iso.refl _) (Iso.refl _) (refl_hom_comp_overSpecHom φ)).obj K') =
      ∑ᶠ u : {u // φ.mapFieldPoints _ u = y}, weilStalkTraceAlternatingSum l (n + 1) _
        (frobeniusFixedPointsReflOfFieldPoint (X := overSpec Y) n u.1).2.2 K' := by
  classical
  rw [weilShriekTraceFunction l (Iso.refl _) (Iso.refl _) (refl_hom_comp_overSpecHom φ)
    ⟨1, Nat.one_pos, Iso.pow_refl 1⟩ K' (n + 1), ← finsum_eq_sum_of_fintype]
  exact (finsum_comp_equiv (fiberMapFieldPointsEquiv φ n y)).symm

variable {ι : End (𝟙_ (GeometricPointMod l (AlgebraicClosure k₀))) →+ PadicAlgCl l}

/-- If the local traces of `K'` are, through `ι`, the trace function of `φ^* K`, then at the image
`φ(u)` of a rational point `u` of `Y` along a monomorphism `φ`, `ι` of the local trace of `φ_! K'`
is the trace function of `K`. -/
theorem map_weilStalkTraceAlternatingSum_weilLowerShriek_mapFieldPoints (φ : Y ⟶ X) [Mono φ]
    [φ.IsOver (Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X)
    (K' : WeilBoundedConstructible l (Iso.refl (overSpec (k₀ := k₀) Y)).hom)
    (hK' : ∀ (n : ℕ)
      (u : (Y ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1))),
      ι (weilStalkTraceAlternatingSum l (n + 1) _
        (frobeniusFixedPointsReflOfFieldPoint (X := overSpec Y) n u).2.2 K') =
        ((WeilComplex.upperStar φ).obj K).traceFunction (n + 1) u) (n : ℕ)
    (u : (Y ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1))) :
    ι (weilStalkTraceAlternatingSum l (n + 1) _
        (frobeniusFixedPointsReflOfFieldPoint (X := overSpec X) n (φ.mapFieldPoints _ u)).2.2
        ((weilLowerShriek l (Iso.refl _) (Iso.refl _) (refl_hom_comp_overSpecHom φ)).obj K')) =
      K.traceFunction (n + 1) (φ.mapFieldPoints _ u) := by
  have : Unique {u' // φ.mapFieldPoints _ u' = φ.mapFieldPoints _ u} :=
    ⟨⟨u, rfl⟩, fun v ↦ Subtype.ext (Scheme.Hom.mapFieldPoints_injective φ v.2)⟩
  rw [weilStalkTraceAlternatingSum_weilLowerShriek_overSpecHom, finsum_unique,
    Unique.default_eq (⟨u, rfl⟩ : {u' // φ.mapFieldPoints _ u' = φ.mapFieldPoints _ u}), hK',
    traceFunction_upperStar]

/-- At a rational point `y` of `X` not coming from `Y`, the local trace of `φ_! K'` vanishes. -/
theorem weilStalkTraceAlternatingSum_weilLowerShriek_of_notMem_range (φ : Y ⟶ X)
    [φ.IsOver (Spec (CommRingCat.of k₀))]
    (K' : WeilBoundedConstructible l (Iso.refl (overSpec (k₀ := k₀) Y)).hom) (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1)))
    (hy : y ∉ Set.range (φ.mapFieldPoints _)) :
    weilStalkTraceAlternatingSum l (n + 1) _
        (frobeniusFixedPointsReflOfFieldPoint (X := overSpec X) n y).2.2
        ((weilLowerShriek l (Iso.refl _) (Iso.refl _) (refl_hom_comp_overSpecHom φ)).obj K') =
      0 := by
  have : IsEmpty {u // φ.mapFieldPoints _ u = y} := ⟨fun u ↦ hy ⟨u.1, u.2⟩⟩
  rw [weilStalkTraceAlternatingSum_weilLowerShriek_overSpecHom, finsum_of_isEmpty]

end LowerShriek

/-! ### The open–closed dévissage -/
variable {U X Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))]
  (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
  {ι : End (𝟙_ (GeometricPointMod l (AlgebraicClosure k₀))) →+ PadicAlgCl l}

/-- **Open–closed dévissage of the Grothendieck–Lefschetz formula.** For an open immersion
`j : U ↪ X` and a closed immersion `i : Z ↪ X` onto its complement, the formula for `j^*K` and
`i^*K` gives the formula for `K`: the cohomological side is additive along the open–closed
triangle `Ra_{U!} j^*K → Ra_{X!} K → Ra_{Z!} i^*K →`, and the rational points of `X` are those of
`U` and of `Z`. -/
theorem SatisfiesLefschetz.of_openClosed (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {K : WeilComplex k₀ l X} (hU : SatisfiesLefschetz ((upperStar j).obj K))
    (hZ : SatisfiesLefschetz ((upperStar i).obj K)) : SatisfiesLefschetz K := fun n ↦ by
  obtain ⟨α, β, γ, hT⟩ := exists_distTriang_derivedLowerShriek_structure_openClosed j i hij K
  refine ((finsum_trace_cohomologyFrobeniusModule_eq_add_of_distTriang _ hT (n + 1)).trans
    (congrArg₂ (· + ·) (hU n) (hZ n))).trans ?_
  rw [Scheme.Hom.finsum_fieldPoints_eq_add_of_openClosed (k₀ := k₀) j i hij]
  exact congrArg₂ (· + ·) (finsum_congr fun u ↦ traceFunction_upperStar j K _ u)
    (finsum_congr fun z ↦ traceFunction_upperStar i K _ z)

/-- **Open–closed dévissage of the local comparison.** For an open immersion `j : U ↪ X` and a
closed immersion `i : Z ↪ X` onto its complement, local comparisons for `j^*K` (through `K'_U`)
and `i^*K` (through `K'_Z`) give a local comparison for `K`, through the direct sum of the Weil
lower shriek images `j_! K'_U` and `i_! K'_Z`: at a rational point of `X`, exactly one of the two
contributes, with the trace function of `K`. -/
theorem HasLocalWeilObjectComparison.of_openClosed (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {K : WeilComplex k₀ l X} (hU : HasLocalWeilObjectComparison ι ((upperStar j).obj K))
    (hZ : HasLocalWeilObjectComparison ι ((upperStar i).obj K)) :
    HasLocalWeilObjectComparison ι K := by
  obtain ⟨KU, hKU⟩ := hU
  obtain ⟨KZ, hKZ⟩ := hZ
  obtain ⟨B, hB, -⟩ := WeilBoundedConstructible.exists_weilStalkTraceAlternatingSum_eq_add l
    (Iso.refl (overSpec (k₀ := k₀) X))
    ((weilLowerShriek l (Iso.refl _) (Iso.refl _) (refl_hom_comp_overSpecHom j)).obj KU)
    ((weilLowerShriek l (Iso.refl _) (Iso.refl _) (refl_hom_comp_overSpecHom i)).obj KZ)
  refine ⟨B, fun n y ↦ ?_⟩
  have hy := Scheme.Hom.mem_range_mapFieldPoints_iff_not_of_openClosed (k₀ := k₀) j i hij y
  rw [hB, map_add]
  by_cases h : y ∈ Set.range (j.mapFieldPoints _)
  · obtain ⟨u, rfl⟩ := h
    rw [map_weilStalkTraceAlternatingSum_weilLowerShriek_mapFieldPoints j K KU hKU,
      weilStalkTraceAlternatingSum_weilLowerShriek_of_notMem_range i KZ n _
        (fun h' ↦ hy.1 h' ⟨u, rfl⟩), map_zero, add_zero]
  · obtain ⟨z, rfl⟩ := hy.2 h
    rw [map_weilStalkTraceAlternatingSum_weilLowerShriek_mapFieldPoints i K KZ hKZ,
      weilStalkTraceAlternatingSum_weilLowerShriek_of_notMem_range j KU n _ h, map_zero,
      zero_add]

/-- **Open–closed dévissage of the comparison.** For an open immersion `j : U ↪ X` and a closed
immersion `i : Z ↪ X` onto its complement, comparisons for `j^*K` and `i^*K` give a comparison
for `K`: by `hasWeilObjectComparison_iff`, it is the dévissage of the local comparison and of the
Grothendieck–Lefschetz formula. -/
theorem HasWeilObjectComparison.of_openClosed (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {K : WeilComplex k₀ l X} (hU : HasWeilObjectComparison ι ((upperStar j).obj K))
    (hZ : HasWeilObjectComparison ι ((upperStar i).obj K)) :
    HasWeilObjectComparison ι K :=
  (hasWeilObjectComparison_iff K).2
    ⟨.of_openClosed j i hij hU.hasLocalWeilObjectComparison hZ.hasLocalWeilObjectComparison,
      .of_openClosed j i hij hU.satisfiesLefschetz hZ.satisfiesLefschetz⟩

end WeilComplex

/-! ### Weil sheaves -/

namespace WeilSheaf

open WeilComplex ProEtale.CondensedRing

variable {U X Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))]
  (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
  {ι : End (𝟙_ (GeometricPointMod l (AlgebraicClosure k₀))) →+ PadicAlgCl l}

/-- Open–closed dévissage of the Grothendieck–Lefschetz formula for a Weil sheaf `G` on `X`,
from the formula for the Weil sheaves `j^*G` and `i^*G`. -/
theorem satisfiesLefschetz_toComplex_of_openClosed (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {G : WeilSheaf k₀ l X} (hU : SatisfiesLefschetz (toComplex.obj ((upperStar j).obj G)))
    (hZ : SatisfiesLefschetz (toComplex.obj ((upperStar i).obj G))) :
    SatisfiesLefschetz (toComplex.obj G) :=
  .of_openClosed j i hij (hU.of_iso ((toComplexCompUpperStarIso j).app G).symm)
    (hZ.of_iso ((toComplexCompUpperStarIso i).app G).symm)

/-- Open–closed dévissage of the local comparison for a Weil sheaf `G` on `X`, from the local
comparisons for the Weil sheaves `j^*G` and `i^*G`. -/
theorem hasLocalWeilObjectComparison_toComplex_of_openClosed
    (hij : Set.range i.base = (Set.range j.base)ᶜ) {G : WeilSheaf k₀ l X}
    (hU : HasLocalWeilObjectComparison ι (toComplex.obj ((upperStar j).obj G)))
    (hZ : HasLocalWeilObjectComparison ι (toComplex.obj ((upperStar i).obj G))) :
    HasLocalWeilObjectComparison ι (toComplex.obj G) :=
  .of_openClosed j i hij (hU.of_iso ((toComplexCompUpperStarIso j).app G).symm)
    (hZ.of_iso ((toComplexCompUpperStarIso i).app G).symm)


/-- Open–closed dévissage of the comparison for a Weil sheaf `G` on `X`, from the comparisons for
the Weil sheaves `j^*G` and `i^*G`. -/
theorem hasWeilObjectComparison_toComplex_of_openClosed
    (hij : Set.range i.base = (Set.range j.base)ᶜ) {G : WeilSheaf k₀ l X}
    (hU : HasWeilObjectComparison ι (toComplex.obj ((upperStar j).obj G)))
    (hZ : HasWeilObjectComparison ι (toComplex.obj ((upperStar i).obj G))) :
    HasWeilObjectComparison ι (toComplex.obj G) :=
  .of_openClosed j i hij (hU.of_iso ((toComplexCompUpperStarIso j).app G).symm)
    (hZ.of_iso ((toComplexCompUpperStarIso i).app G).symm)

end WeilSheaf

end AlgebraicGeometry
