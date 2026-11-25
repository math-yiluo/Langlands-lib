/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LisseFiltration
public import WeilConjectures.WeilSheaf.SmoothLisseOpen
public import WeilConjectures.WeilSheaf.Triangle
public import WeilConjectures.ZetaFunction.WeilObjectComparisonOpenClosed

/-!
# Noetherian induction for the comparison of Weil sheaves with Weil objects

The comparison of the Weil sheaves of the zeta-function chapter with the Weil objects of the
trace formula chapter (`AlgebraicGeometry.WeilComplex.HasWeilObjectComparison`) is reduced by
Noetherian induction to lisse Weil sheaves on smooth irreducible schemes.

## Main results

- `AlgebraicGeometry.WeilComplex.HasWeilObjectComparison.of_isZero`: a zero Weil complex has a
  comparison, through a zero Weil object.
- `AlgebraicGeometry.WeilSheaf.hasWeilObjectComparison_toComplex_of_isEmpty`: so does every Weil
  sheaf on the empty scheme.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

attribute [local instance] fact_ringChar_prime_of_finite

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

namespace WeilComplex

open ProEtale.CondensedRing

variable {ι : End (MonoidalCategory.tensorUnit (GeometricPointMod l (AlgebraicClosure k₀))) →+
  PadicAlgCl l}

/-- An element of a `ℤ`-module over a field of characteristic zero which is equal to its
negative is zero. -/
private lemma eq_zero_of_eq_neg {x : PadicAlgCl l} (h : x = -x) : x = 0 := by
  have h2 : (2 : PadicAlgCl l) * x = 0 := by rw [two_mul]; nth_rw 1 [h]; exact neg_add_cancel x
  exact (mul_eq_zero.1 h2).resolve_left two_ne_zero

/-- **Zero Weil complexes have a comparison**, through a zero Weil object: all the traces
vanish. On the side of the Weil complexes, a zero complex is isomorphic to its shift by `1`,
whose traces are the negatives of its own. -/
theorem HasWeilObjectComparison.of_isZero {K : WeilComplex k₀ l X} (hK : IsZero K) :
    HasWeilObjectComparison ι K := by
  obtain ⟨Z, -, -, -, hZ, -⟩ := WeilBoundedConstructible.exists_isDistTriang_isZero l
    (weilUnit l (Iso.refl (overSpec (k₀ := k₀) X)))
  have e : K ≅ K⟦(1 : ℤ)⟧ := hK.iso ((shiftFunctor _ (1 : ℤ)).map_isZero hK)
  refine ⟨Z, fun n ↦ ?_, fun n y ↦ ?_⟩
  · rw [weilStalkTraceAlternatingSum_weilCompactSupportCohomology_eq_zero_of_isZero l _ n hZ,
      map_zero]
    refine (eq_zero_of_eq_neg ?_).symm
    have h := (finsum_trace_compactlySupportedCohomology_congr e (n + 1)).trans
      (finsum_trace_compactlySupportedCohomology_shift K 1 (n + 1))
    rw [Int.negOnePow_one, Units.val_neg, Units.val_one, neg_smul, one_smul] at h
    exact h
  · rw [weilStalkTraceAlternatingSum_eq_zero_of_isZero l _ _ _ hZ, map_zero]
    refine (eq_zero_of_eq_neg ?_).symm
    have h := (traceFunction_eq_of_iso e (n + 1) y).trans (traceFunction_shift K 1 (n + 1) y)
    rw [Int.negOnePow_one, Units.val_neg, Units.val_one, neg_smul, one_smul] at h
    exact h

end WeilComplex

namespace WeilSheaf

open ProEtale.CondensedRing

variable {ι : End (MonoidalCategory.tensorUnit (GeometricPointMod l (AlgebraicClosure k₀))) →+
  PadicAlgCl l}

omit [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] in
/-- Every Weil sheaf on the empty scheme is zero: its underlying sheaf lives on the empty
geometric fibre. -/
theorem isZero_of_isEmpty [IsEmpty X] (G : WeilSheaf k₀ l X) : IsZero G := by
  have : IsEmpty (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    ⟨fun x ↦ isEmptyElim ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj.base x)⟩
  refine isZero_iff_isZero_carrier.2 ?_
  refine (IsZero.iff_id_eq_zero _).2 (Mod.hom_ext _ _ ?_)
  refine Sheaf.hom_ext (NatTrans.ext (funext fun T ↦ ?_))
  have : IsEmpty T.unop.left := ⟨fun x ↦ isEmptyElim
    (α := (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) (T.unop.hom.base x)⟩
  exact (Scheme.ProEt.isTerminalSectionsOfIsEmpty _ T.unop).hom_ext _ _

/-- On the empty scheme every Weil sheaf has a comparison along any `ι`. -/
theorem hasWeilObjectComparison_toComplex_of_isEmpty [IsEmpty X] (G : WeilSheaf k₀ l X) :
    WeilComplex.HasWeilObjectComparison ι (toComplex.obj G) :=
  .of_isZero (toComplex.map_isZero (isZero_of_isEmpty G))

variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]

/-- The generic case of the Noetherian induction: every lisse Weil sheaf on a smooth irreducible
separated `k₀`-scheme of finite type has a comparison along `ι`. -/
def LisseComparisonHolds
    (ι : End (MonoidalCategory.tensorUnit (GeometricPointMod l (AlgebraicClosure k₀))) →+
      PadicAlgCl l) : Prop :=
  ∀ (V : Scheme.{u}) [V.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (V ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (V ↘ Spec (CommRingCat.of k₀))] [Smooth (V ↘ Spec (CommRingCat.of k₀))]
    [IrreducibleSpace V] [IsAffine V] (G : WeilSheaf k₀ l V), G.IsLisse →
      WeilComplex.HasWeilObjectComparison ι (toComplex.obj G)

/-- **Reduction.** For a surjective closed immersion `r : Z ↪ X` (for instance `X_red ↪ X`), a
Weil sheaf `G` on `X` has a comparison as soon as `r^* G` has: `r` is a closed immersion onto the
complement of the empty open subscheme, on which every Weil sheaf has a comparison. -/
theorem hasWeilObjectComparison_toComplex_of_surjective (r : Z ⟶ X) [IsClosedImmersion r]
    [r.IsOver (Spec (CommRingCat.of k₀))] (hr : Function.Surjective r.base)
    (G : WeilSheaf k₀ l X)
    (h : WeilComplex.HasWeilObjectComparison ι (toComplex.obj ((WeilSheaf.upperStar r).obj G))) :
    WeilComplex.HasWeilObjectComparison ι (toComplex.obj G) := by
  have : IsEmpty (⊥ : X.Opens).toScheme := ⟨fun x ↦ x.2⟩
  refine hasWeilObjectComparison_toComplex_of_openClosed (⊥ : X.Opens).ι r ?_
    (hasWeilObjectComparison_toComplex_of_isEmpty _) h
  rw [hr.range_eq, Scheme.Opens.range_ι]
  simp

/-- **The inductive step**, for a reduced scheme: if every Weil sheaf on every proper closed
subscheme of a reduced `Z` has a comparison, and lisse Weil sheaves on smooth irreducible
schemes have comparisons, then every Weil sheaf on `Z` has a comparison. Indeed `Z`, if
nonempty, has a nonempty smooth irreducible open `V` on which `G` is lisse
(`AlgebraicGeometry.WeilSheaf.exists_opens_smooth_irreducibleSpace_isLisse`), and the open–closed
dévissage along `V` and its reduced complement applies. -/
theorem hasWeilObjectComparison_toComplex_of_isReduced (h : LisseComparisonHolds ι)
    [IsReduced X]
    (hX : ∀ (W : Scheme.{u}) [W.Over (Spec (CommRingCat.of k₀))]
      [IsSeparated (W ↘ Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of k₀))]
      [QuasiCompact (W ↘ Spec (CommRingCat.of k₀))] (i : W ⟶ X) [IsClosedImmersion i],
      Set.range i.base ≠ Set.univ → ∀ G : WeilSheaf k₀ l W,
        WeilComplex.HasWeilObjectComparison ι (toComplex.obj G))
    (G : WeilSheaf k₀ l X) : WeilComplex.HasWeilObjectComparison ι (toComplex.obj G) := by
  rcases isEmpty_or_nonempty X with hX₀ | hX₀
  · exact hasWeilObjectComparison_toComplex_of_isEmpty G
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k₀))
  obtain ⟨V, hVa, hVs, hVi, hVl⟩ := exists_opens_smooth_irreducibleSpace_isLisse G
  have : IsAffine V := hVa
  obtain ⟨v⟩ := hVi.toNonempty
  set C : TopologicalSpace.Closeds X := ⟨(V : Set X)ᶜ, V.isOpen.isClosed_compl⟩
  set i := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  let : (Scheme.IdealSheafData.vanishingIdeal C).subscheme.Over (Spec (CommRingCat.of k₀)) :=
    ⟨i ≫ X ↘ Spec (CommRingCat.of k₀)⟩
  have : i.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : IsSeparated ((Scheme.IdealSheafData.vanishingIdeal C).subscheme ↘
      Spec (CommRingCat.of k₀)) := inferInstanceAs (IsSeparated (i ≫ _))
  have : LocallyOfFiniteType ((Scheme.IdealSheafData.vanishingIdeal C).subscheme ↘
      Spec (CommRingCat.of k₀)) := inferInstanceAs (LocallyOfFiniteType (i ≫ _))
  have : QuasiCompact ((Scheme.IdealSheafData.vanishingIdeal C).subscheme ↘
      Spec (CommRingCat.of k₀)) := inferInstanceAs (QuasiCompact (i ≫ _))
  have hrange : Set.range i.base = (Set.range V.ι.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_vanishingIdeal_subschemeι, Scheme.Opens.range_ι]
    rfl
  have : IsSeparated (V.toScheme ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (IsSeparated (V.ι ≫ _))
  have : LocallyOfFiniteType (V.toScheme ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (V.ι ≫ _))
  have : QuasiCompact (V.toScheme ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiCompact (V.ι ≫ _))
  refine hasWeilObjectComparison_toComplex_of_openClosed V.ι i hrange
    (h V.toScheme _ hVl) (hX _ i ?_ _)
  rw [hrange]
  intro hu
  have hv : V.ι.base v ∈ (Set.range V.ι.base)ᶜ := hu ▸ Set.mem_univ _
  exact hv (Set.mem_range_self v)

/-- **Noetherian induction**: if lisse Weil sheaves on smooth irreducible separated `k₀`-schemes
of finite type have comparisons, then so does every Weil sheaf on `X`. The induction runs over
the closed subsets of `X` which are the ranges of closed immersions, as in
`ProEtale.CondensedRing.shriekTraceFunctionAt_of_exists_isOpenImmersion`: a scheme `Z` is first
replaced by its reduction
(`AlgebraicGeometry.WeilSheaf.hasWeilObjectComparison_toComplex_of_surjective`), and then the
inductive step
`AlgebraicGeometry.WeilSheaf.hasWeilObjectComparison_toComplex_of_isReduced` applies. -/
theorem hasWeilObjectComparison_toComplex_of_lisseComparisonHolds (h : LisseComparisonHolds ι)
    (G : WeilSheaf k₀ l X) : WeilComplex.HasWeilObjectComparison ι (toComplex.obj G) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k₀))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of k₀))
  have : IsNoetherian X := ⟨⟩
  have key (T : TopologicalSpace.Closeds X) : ∀ (Z : Scheme.{u})
      [Z.Over (Spec (CommRingCat.of k₀))] [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
      [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))] (iZ : Z ⟶ X) [IsClosedImmersion iZ],
      Set.range iZ.base = T → ∀ G : WeilSheaf k₀ l Z,
        WeilComplex.HasWeilObjectComparison ι (toComplex.obj G) := by
    induction T using WellFoundedLT.induction with
    | _ T ih =>
    intro Z _ _ _ _ iZ _ hT G
    -- the reduction `r : Z_red ↪ Z`
    set r := (Scheme.IdealSheafData.vanishingIdeal (⊤ : TopologicalSpace.Closeds Z)).subschemeι
    let : (Scheme.IdealSheafData.vanishingIdeal
        (⊤ : TopologicalSpace.Closeds Z)).subscheme.Over (Spec (CommRingCat.of k₀)) :=
      ⟨r ≫ Z ↘ Spec (CommRingCat.of k₀)⟩
    have : r.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
    have : IsSeparated ((Scheme.IdealSheafData.vanishingIdeal
        (⊤ : TopologicalSpace.Closeds Z)).subscheme ↘ Spec (CommRingCat.of k₀)) :=
      inferInstanceAs (IsSeparated (r ≫ _))
    have : LocallyOfFiniteType ((Scheme.IdealSheafData.vanishingIdeal
        (⊤ : TopologicalSpace.Closeds Z)).subscheme ↘ Spec (CommRingCat.of k₀)) :=
      inferInstanceAs (LocallyOfFiniteType (r ≫ _))
    have : QuasiCompact ((Scheme.IdealSheafData.vanishingIdeal
        (⊤ : TopologicalSpace.Closeds Z)).subscheme ↘ Spec (CommRingCat.of k₀)) :=
      inferInstanceAs (QuasiCompact (r ≫ _))
    have hr : Set.range r.base = Set.univ := by
      rw [Scheme.IdealSheafData.range_vanishingIdeal_subschemeι]
      rfl
    have hrs : Function.Surjective r.base := Set.range_eq_univ.1 hr
    refine hasWeilObjectComparison_toComplex_of_surjective r hrs G ?_
    refine hasWeilObjectComparison_toComplex_of_isReduced h
      (fun W _ _ _ _ i _ hi G' ↦ ?_) _
    have : IsClosedImmersion (i ≫ r ≫ iZ) := inferInstance
    refine ih ⟨Set.range (i ≫ r ≫ iZ).base, (i ≫ r ≫ iZ).isClosedEmbedding.isClosed_range⟩ ?_
      W (i ≫ r ≫ iZ) rfl G'
    rw [← SetLike.coe_ssubset_coe, TopologicalSpace.Closeds.coe_mk, ← hT]
    refine Set.ssubset_iff_subset_ne.2 ⟨fun _ ⟨a, ha⟩ ↦ ⟨r.base (i.base a), ha⟩,
      fun he ↦ hi (Set.eq_univ_of_forall fun w ↦ ?_)⟩
    obtain ⟨a, ha⟩ : iZ.base (r.base w) ∈ Set.range (i ≫ r ≫ iZ).base :=
      he ▸ Set.mem_range_self _
    change iZ.base (r.base (i.base a)) = _ at ha
    exact ⟨a, r.isClosedEmbedding.injective (iZ.isClosedEmbedding.injective ha)⟩
  have : IsClosedImmersion (𝟙 X) := inferInstance
  exact key ⊤ X (𝟙 X) (by simp) G

/-- **Extensions.** The Weil sheaves with a comparison along `ι` are closed under extensions:
a short exact sequence `0 → F₁ → F₂ → F₃ → 0` of Weil sheaves gives a distinguished triangle
`F₁ → F₂ → F₃ → F₁[1]` of Weil complexes (`AlgebraicGeometry.WeilSheaf.singleTriangle`). Hence
every Weil sheaf in the closure of a property `P` under filtrations has a comparison as soon as
the Weil sheaves satisfying `P` have. -/
theorem hasWeilObjectComparison_toComplex_of_filtrationClosure
    {P : ObjectProperty (WeilSheaf k₀ l X)}
    (hP : ∀ G, P G → WeilComplex.HasWeilObjectComparison ι (toComplex.obj G))
    {G : WeilSheaf k₀ l X} (hG : P.filtrationClosure G) :
    WeilComplex.HasWeilObjectComparison ι (toComplex.obj G) := by
  induction hG with
  | of_isZero hX => exact .of_isZero (toComplex.map_isZero hX)
  | @of_mono A B i _ _ hi ih =>
    let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i) }
    have h₁ : WeilComplex.HasWeilObjectComparison ι (singleTriangle hS).obj₁ := ih
    have h₃ : WeilComplex.HasWeilObjectComparison ι (singleTriangle hS).obj₃ := hP _ hi
    exact WeilComplex.HasWeilObjectComparison.of_distTriang (singleTriangle hS)
      (singleTriangle_distinguished hS) h₁ h₃

/-- The case of irreducible lisse Weil sheaves of the Noetherian induction: every irreducible
lisse Weil sheaf on a smooth irreducible separated `k₀`-scheme of finite type has a comparison
along `ι`. -/
def IrreducibleLisseComparisonHolds
    (ι : End (MonoidalCategory.tensorUnit (GeometricPointMod l (AlgebraicClosure k₀))) →+
      PadicAlgCl l) : Prop :=
  ∀ (V : Scheme.{u}) [V.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (V ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (V ↘ Spec (CommRingCat.of k₀))] [Smooth (V ↘ Spec (CommRingCat.of k₀))]
    [IrreducibleSpace V] [IsAffine V] (G : WeilSheaf k₀ l V), G.IsIrreducibleLisse →
      WeilComplex.HasWeilObjectComparison ι (toComplex.obj G)

/-- **Jordan–Hölder for lisse Weil sheaves**: a lisse Weil sheaf has a finite filtration by lisse
Weil subsheaves with irreducible lisse quotients
(`AlgebraicGeometry.WeilSheaf.IsLisse.filtrationClosure_isIrreducibleLisse`), so the comparison for
irreducible lisse Weil sheaves gives the comparison for all lisse Weil sheaves. -/
theorem lisseComparisonHolds_of_irreducibleLisseComparisonHolds
    (h : IrreducibleLisseComparisonHolds ι) : LisseComparisonHolds ι :=
  fun V _ _ _ _ _ _ _ _ hG ↦ hasWeilObjectComparison_toComplex_of_filtrationClosure
    (fun H hH ↦ h V H hH) hG.filtrationClosure_isIrreducibleLisse

end WeilSheaf

end AlgebraicGeometry
