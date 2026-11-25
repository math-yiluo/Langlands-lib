/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.WeilSheaf.OpenImmersion

/-!
# Direct images with compact support of Weil sheaves and Weil complexes

Let `f : X ⟶ Y` be a separated quasi-compact morphism locally of finite type of `k₀`-schemes,
with `Y` of finite type and quasi-separated over `k₀`. By Nagata's theorem `f` has a
compactification `X ⟶[i] Z ⟶[g] Y` over `k₀`: an open immersion `i` followed by a proper
morphism `g`. Its base change `X̄ ⟶[ī] Z̄ ⟶[ḡ] Ȳ` to `k̄` is a compactification of `f̄`, and
both `ī` and `ḡ` commute with the geometric Frobenii, since they are defined over `k₀`. The
direct image with compact support of Weil complexes is

`Rf_! := Rḡ_* ∘ ī_! : D(ProEtaleWeilSheaf k₀ l X) ⥤ D(ProEtaleWeilSheaf k₀ l Y)`,

the functor induced by the exact extension by zero `ī_!` of pro-étale Weil sheaves followed by
the total right derived functor of the pushforward `ḡ_*` of pro-étale Weil sheaves
(`AlgebraicGeometry.ProEtaleWeilSheaf.rightDerivedLowerShriek`), for the compactification
chosen by `AlgebraicGeometry.HasCompactification.compactification`. Forgetting the Weil
structures it is the pro-étale `Rf̄_! = Rḡ_* ∘ ī_!` of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`. Since the Frobenius is
built into the categories of pro-étale Weil sheaves, no transport of the compactification along the
Frobenius is needed.

That `Rf_!` carries Weil complexes to Weil complexes is the finiteness theorem for `Rf_!`
(SGA 4½, *Th. finitude*), `AlgebraicGeometry.WeilComplex.objectProperty_rightDerivedLowerShriek`,
deduced from the finiteness of `ī_!` and of `Rḡ_*`. The higher direct images `Rʳf₀!` of Weil
sheaves are the cohomology sheaves of `Rf₀!`. Compactly supported cohomology is defined in
`WeilConjectures.WeilSheaf.Cohomology` from `Rf₀!` along the structure morphism `X ⟶ Spec k₀`.

## Main declarations

- `AlgebraicGeometry.ProEtaleWeilSheaf.rightDerivedLowerShriek`: `Rf_!` on the derived
  categories of pro-étale Weil sheaves, attached to a compactification over `k₀`.
- `AlgebraicGeometry.WeilSheaf.higherLowerShriek` and
  `AlgebraicGeometry.WeilComplex.derivedLowerShriek`: the higher direct images with compact
  support `Rʳf₀!` and the total derived one `Rf₀!`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

section LowerShriek

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

/-- The scheme `Z` of a compactification `X ⟶[i] Z ⟶[g] Y` of a morphism of `k₀`-schemes is a
`k₀`-scheme through `g`. -/
noncomputable abbrev Compactification.over {f : X ⟶ Y} (c : Compactification f) :
    c.Z.Over (Spec (CommRingCat.of k₀)) :=
  ⟨c.g ≫ Y ↘ Spec (CommRingCat.of k₀)⟩

attribute [local instance] Compactification.over

instance Compactification.isOver_g_finiteField {f : X ⟶ Y} (c : Compactification f) :
    c.g.IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨rfl⟩

instance Compactification.isOver_i_finiteField {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))]
    (c : Compactification f) : c.i.IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨show c.i ≫ c.g ≫ Y ↘ Spec (CommRingCat.of k₀) = _ by
    rw [← Category.assoc, ← c.comm, comp_over]⟩

variable (k₀ l) in
/-- The direct image with compact support `Rf_! = Rḡ_* ∘ ī_!` on the derived categories of
pro-étale Weil sheaves, attached to a compactification `X ⟶[i] Z ⟶[g] Y` of a morphism of
`k₀`-schemes: the functor induced by the exact extension by zero along `i` followed by the
total right derived functor of the pushforward along `g`, both taken on pro-étale Weil sheaves
on the geometric fibers. -/
noncomputable def ProEtaleWeilSheaf.rightDerivedLowerShriek (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] (c : Compactification f) :
    _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l X) ⥤
      _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l Y) :=
  (ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory ⋙
    (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor

omit [Finite k₀] [X.Over (Spec (CommRingCat.of k₀))] in
/-- A separated quasi-compact morphism locally of finite type of `k₀`-schemes, whose target is
quasi-compact and quasi-separated over `k₀`, has a compactification (Nagata). -/
lemma hasCompactification_of_over (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] : HasCompactification f :=
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of k₀))
  have : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (CommRingCat.of k₀))
  inferInstance

/-- **Finiteness for the direct image with compact support of Weil complexes** (SGA 4½,
*Th. finitude*): `Rf_!` carries Weil complexes, bounded with constructible cohomology, to
Weil complexes. For `Rf_! = Rḡ_* ∘ ī_!` this follows from the exactness of `ī_!`, which
preserves constructibility (`AlgebraicGeometry.WeilSheaf.isAdicConstructibleSheaf_extensionByZero`),
and from the finiteness of `Rḡ_*`
(`AlgebraicGeometry.WeilComplex.objectProperty_rightDerivedLowerStar`). The target is assumed
quasi-compact over `k₀`: over `Y = ⊔ₙ Spec k₀` the direct image of `ℚ̄_ℓ` along the proper
morphism `⊔ₙ ℙⁿ ⟶ Y` is not bounded. -/
theorem WeilComplex.objectProperty_rightDerivedLowerShriek (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [hf : HasCompactification f]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    (K : _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l X))
    (hK : WeilComplex.objectProperty k₀ l X K) :
    WeilComplex.objectProperty k₀ l Y ((ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f
      (HasCompactification.compactification f)).obj K) := by
  let c := HasCompactification.compactification f
  -- `c.Z` is noetherian, being proper over the noetherian `Y`; so the open immersion `c.i` is
  -- quasi-compact.
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of k₀))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of k₀))
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have : TopologicalSpace.NoetherianSpace X := c.i.isOpenEmbedding.isInducing.noetherianSpace
  have hK' : WeilComplex.objectProperty k₀ l c.Z
      ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory.obj K) :=
    ⟨(ProEtaleWeilSheaf.extensionByZero k₀ l c.i).bounded_mapDerivedCategory_obj hK.1,
      fun n ↦ (WeilSheaf.objectProperty k₀ l c.Z).prop_of_iso
        (((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategoryHomologyFunctorIso
          n).app K) (WeilSheaf.isAdicConstructibleSheaf_extensionByZero c.i _ (hK.2 n))⟩
  unfold ProEtaleWeilSheaf.rightDerivedLowerShriek
  rw [Functor.comp_obj]
  exact WeilComplex.objectProperty_rightDerivedLowerStar c.g _ hK'

-- TODO(unify): sk-thm-sf-package
variable (k₀ l) in
/-- The total derived direct image with compact support `Rf₀!` along a separated quasi-compact
morphism `f : X ⟶ Y` locally of finite type of `k₀`-schemes, with `Y` of finite type and
quasi-separated over `k₀`: the functor `ProEtaleWeilSheaf.rightDerivedLowerShriek` attached to
the chosen compactification of `f`, restricted to Weil complexes. -/
noncomputable def WeilComplex.derivedLowerShriek (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] :
    WeilComplex k₀ l X ⥤ WeilComplex k₀ l Y :=
  (WeilComplex.objectProperty k₀ l X).liftFullSubcategory (WeilComplex.objectProperty k₀ l Y)
    (ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f
      (HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)))
    (WeilComplex.objectProperty_rightDerivedLowerShriek f
      (hf := hasCompactification_of_over (k₀ := k₀) f))

-- TODO(unify): sk-thm-sf-package
variable (k₀ l) in
/-- The `r`-th higher direct image with compact support `Rʳf₀!` along a separated quasi-compact
morphism locally of finite type of `k₀`-schemes, with target of finite type and
quasi-separated over `k₀`: the `r`-th cohomology sheaf of `Rf₀!`, in cohomological
indexing. -/
noncomputable def WeilSheaf.higherLowerShriek (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (r : ℕ) :
    WeilSheaf k₀ l X ⥤ WeilSheaf k₀ l Y :=
  WeilSheaf.toComplex ⋙ WeilComplex.derivedLowerShriek k₀ l f ⋙ WeilComplex.homologySheaf r

instance (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] (c : Compactification f) :
    (ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c).Additive := by
  unfold ProEtaleWeilSheaf.rightDerivedLowerShriek
  infer_instance

instance (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] :
    (WeilComplex.derivedLowerShriek k₀ l f).Additive :=
  ObjectProperty.liftFullSubcategory_additive _ _ _ _

noncomputable instance (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
    (c : Compactification f) :
    (ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c).CommShift ℤ := by
  unfold ProEtaleWeilSheaf.rightDerivedLowerShriek
  infer_instance

/-- The direct image with compact support is a triangulated functor. -/
instance (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] (c : Compactification f) :
    (ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c).IsTriangulated := by
  unfold ProEtaleWeilSheaf.rightDerivedLowerShriek
  infer_instance

noncomputable instance (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] :
    (WeilComplex.derivedLowerShriek k₀ l f).CommShift ℤ :=
  ObjectProperty.commShiftLiftFullSubcategory _ _ _ _

/-- The direct image with compact support of Weil complexes is a triangulated functor. -/
instance (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    (WeilComplex.derivedLowerShriek k₀ l f).IsTriangulated :=
  ObjectProperty.isTriangulated_liftFullSubcategory _ _ _ _

instance (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (r : ℕ) :
    (WeilSheaf.higherLowerShriek k₀ l f r).Additive := by
  unfold WeilSheaf.higherLowerShriek
  infer_instance

end LowerShriek

end AlgebraicGeometry
