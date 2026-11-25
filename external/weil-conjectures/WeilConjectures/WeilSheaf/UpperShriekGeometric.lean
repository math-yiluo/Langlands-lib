/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointForget
public import WeilConjectures.PoincareDuality.DualizingComplexCompactification
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseLocallyFree
public import WeilConjectures.SixFunctors.ProEtale.Adic.ProperLowerStarCondensedAdjoint
public import WeilConjectures.WeilSheaf.CondensedModelCompactSupport
public import WeilConjectures.WeilSheaf.LowerShriekIndependence
public import WeilConjectures.WeilSheaf.Operations
public import WeilConjectures.WeilSheaf.ProperLowerStarAdjoint
public import WeilConjectures.WeilSheaf.SixFunctors.WeilGeometricHomConstructibility

/-!
# The exceptional inverse image of Weil complexes lies over the geometric one

Let `X` be a separated `k₀`-scheme of finite type with structure morphism `a : X ⟶ Spec k₀`, and
let `R` be a right adjoint of the direct image with compact support
`Ra_! : WeilComplex X ⥤ WeilComplex k₀` of Weil complexes. We show that the underlying complex on
the geometric fibre `X̄` of `R ℚ̄_ℓ` is the dualizing complex `ω_X̄` of `X̄` over `k̄`
(`AlgebraicGeometry.WeilComplex.nonempty_nativeGeometricForget_obj_iso_of_adjunction`,
blueprint `prose-10-20`).

## Proof

Let `X ⟶[i] Z ⟶[g] Spec k₀` be the compactification of `a` defining `Ra_!`, so that
`Ra_! ≅ Rg_* ∘ i_!`.

* `Rg_*` on Weil complexes is a left adjoint, and any right adjoint `R_g` lies over a right
  adjoint `ḡ^!` of `Rḡ_*` on `Dᵇc(Z̄)`
  (`CategoryTheory.Endofunctor.IsoAlgebra.nonempty_forget_obj_iso_of_adjunction`); in the
  condensed model, `ḡ^!` is the exceptional inverse image of
  `ProEtale.CondensedRing.boundedConstructibleLowerStar`
  (`AlgebraicGeometry.ProEtale.exists_adjunction_boundedConstructibleAdicRightDerivedLowerStar`).
* By uniqueness of adjoints `R ≅ R_g ⋙ i^*`, and `i^*` commutes with forgetting the Weil
  structure. So the underlying complex of `R ℚ̄_ℓ` is `ī^* ḡ^! ℚ̄_ℓ = Rā^!(c̄) ℚ̄_ℓ` for the
  compactification `c̄` of `X̄ ⟶ (Spec k₀)̄` obtained by base change.
* As `(Spec k₀)̄ ≅ Spec k̄`, this is `ω_X̄`
  (`ProEtale.CondensedRing.nonempty_upperShriekOfCompactification_obj_unit_iso`).

The proof does not use the comparison of internal homs of Weil complexes.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

open ProEtale

attribute [local instance] Compactification.over

-- `Spec k₀` lies over itself through the identity, so that the structure-morphism instances
-- `(X ↘ S).IsOver S` apply.
attribute [local instance 1100] CategoryTheory.instOverClass

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

variable (k₀) in
/-- The geometric fibre `(Spec k₀)̄` of `Spec k₀`, as a scheme over `k̄`; its structure morphism is
an isomorphism. -/
noncomputable abbrev pointGeometricFiberOver : Over (Spec (.of (AlgebraicClosure k₀))) :=
  Over.mk (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure

variable (X) in
/-- The base change `X̄ ⟶ (Spec k₀)̄` of the structure morphism, as a morphism over `k̄`. -/
noncomputable abbrev geometricFiberStructureMorphism :
    Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure ⟶
      pointGeometricFiberOver k₀ :=
  Over.homMk (Scheme.Hom.geometricFiberMap (X ↘ Spec (CommRingCat.of k₀))
    (comp_over (X ↘ Spec (CommRingCat.of k₀)) (Spec (CommRingCat.of k₀)))) (by
      simp [Scheme.Hom.geometricFiberToAlgebraicClosure, Scheme.Hom.geometricFiberMap])

variable (X) in
/-- The compactification of `X̄ ⟶ (Spec k₀)̄` obtained by base change from the compactification
chosen by `AlgebraicGeometry.WeilComplex.derivedLowerShriek`. -/
noncomputable abbrev geometricFiberCompactification :
    Compactification (geometricFiberStructureMorphism (k₀ := k₀) X).left :=
  (structureMorphismCompactification (k₀ := k₀) X).geometricFiber
    (comp_over (X ↘ Spec (CommRingCat.of k₀)) (Spec (CommRingCat.of k₀)))


section Instances

variable (Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of k₀))]

instance instIsSeparatedHomScheme_upperShriekGeometric
    [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))] :
    IsSeparated (Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (IsSeparated (pullback.snd _ _))

instance instLocallyOfFiniteType_upperShriekGeometric
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] :
    LocallyOfFiniteType
      (Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))

instance instQuasiCompactHomScheme_upperShriekGeometric
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] :
    QuasiCompact (Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd _ _))

end Instances

section Relative

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f]

/-- The base change `f̄ : X̄ ⟶ Ȳ` of `f` to the geometric fibres, as a morphism over `k̄`. -/
noncomputable abbrev geometricFiberHom :
    Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure ⟶
      Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure :=
  Over.homMk (Scheme.Hom.geometricFiberMap f (comp_over f (Spec (CommRingCat.of k₀))))
    (Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure _ _)

/-- The compactification of `f̄ : X̄ ⟶ Ȳ` obtained by base change from the compactification of `f`
chosen by `AlgebraicGeometry.WeilComplex.derivedLowerShriek`. -/
noncomputable abbrev geometricFiberHomCompactification :
    Compactification (geometricFiberHom (k₀ := k₀) f).left :=
  (HasCompactification.compactification f
    (hf := hasCompactification_of_over (k₀ := k₀) f)).geometricFiber
      (comp_over f (Spec (CommRingCat.of k₀)))

/-- The underlying complex on the geometric fibre `Ȳ` of a Weil complex `L` on `Y`, as a bounded
constructible complex of `ℚ̄_ℓ`-modules in the condensed model. -/
noncomputable abbrev geometricFiberBoundedConstructibleObj (L : WeilComplex k₀ l Y) :
    BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
      (Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left) :=
  ⟨(adicSheafDerivedEquivCondensedMod l
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.obj (forget.obj L),
    (boundedConstructibleAdic_iff_boundedConstructible l k₀ (AlgebraicClosure k₀)
      (Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure) _).1
      ((objectProperty_iff (X := Y) L.obj).1 L.property)⟩

/-- **The Weil exceptional inverse image lies over the geometric one.** For a separated morphism
of finite type `f : X ⟶ Y` of `k₀`-schemes, a right adjoint `R` of `Rf₀!` on Weil complexes and a
Weil complex `L` on `Y`, the underlying complex of `R L` on `X̄`, in the condensed model, is
`Rf̄^!(c̄)` of the underlying complex of `L`, for the compactification `c̄` of `f̄ : X̄ ⟶ Ȳ`
obtained by base change. -/
theorem nonempty_adicSheafDerivedEquivCondensedMod_forget_obj_iso_upperShriekOfCompactification
    {R : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X} (adj : derivedLowerShriek k₀ l f ⊣ R)
    (L : WeilComplex k₀ l Y) :
    Nonempty ((adicSheafDerivedEquivCondensedMod l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.obj (forget.obj (R.obj L)) ≅
      ((CondensedRing.boundedConstructibleUpperShriekOfCompactification l
        (geometricFiberHomCompactification (k₀ := k₀) f)).obj
          (geometricFiberBoundedConstructibleObj L)).obj) := by
  let c := HasCompactification.compactification f
    (hf := hasCompactification_of_over (k₀ := k₀) f)
  let cb := geometricFiberHomCompactification (k₀ := k₀) f
  have : IsProper c.g := c.isProper
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have hk := ringChar_algebraicClosure_ne (k₀ := k₀) (l := l)
  have hR : ∀ K, DerivedCategory.boundedConstructibleAdic l cb.overObj.left K →
      DerivedCategory.boundedConstructibleAdic l
        (Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left
        ((adicLowerStar l cb.overG.left).rightDerivedFunctor.obj K) := fun _ hK ↦
    boundedConstructibleAdic_rightDerivedFunctor_adicLowerStar_obj
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure hk _ hK
  -- the geometric adjunction `Rḡ_* ⊣ ḡ^!`, transported from the condensed model
  obtain ⟨R', adjR', hR'⟩ :=
    exists_adjunction_boundedConstructibleAdicRightDerivedLowerStar l k₀ cb.overG hR
  have : IsProper (Scheme.Hom.geometricFiberMap c.g (comp_over c.g (Spec (CommRingCat.of k₀)))) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper) c.g _ ‹_›
  have hPC_F := WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff
    (k₀ := k₀) (l := l) (X := c.Z)
  have hPD_G (K) (hK : DerivedCategory.boundedConstructibleAdic l
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber K) :=
    (WeilSheaf.boundedConstructibleAdic_frobeniusPullback_mapDerivedCategory_obj_iff
      (k₀ := k₀) (l := l) (X := Y) K).2 hK
  have hcoprod := ProEtale.preservesColimit_discrete_rightDerivedFunctor_adicLowerStar (l := l)
    (Scheme.Hom.geometricFiberMap c.g (comp_over c.g (Spec (CommRingCat.of k₀))))
  -- `Rg_*` on Weil complexes is a left adjoint
  have : (derivedLowerStar (k₀ := k₀) (l := l) c.g).IsLeftAdjoint :=
    IsoAlgebra.isLeftAdjoint_liftFullSubcategory_rightDerivedFunctor
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l c.g (comp_over c.g _))
      (DerivedCategory.boundedConstructibleAdic l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (DerivedCategory.boundedConstructibleAdic l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (fun _ hK ↦ hK.1) (fun K n hK ↦ ObjectProperty.le_shift _ n K hK) hPC_F hPD_G hR
      adjR'.isLeftAdjoint hcoprod
      (WeilComplex.objectProperty k₀ l c.Z) (WeilComplex.objectProperty k₀ l _)
      (WeilComplex.objectProperty_iff (X := c.Z)) (WeilComplex.objectProperty_iff (X := _))
      (WeilComplex.objectProperty_rightDerivedLowerStar c.g)
  let adjg := Adjunction.ofIsLeftAdjoint (derivedLowerStar (k₀ := k₀) (l := l) c.g)
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of k₀))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of k₀))
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have : TopologicalSpace.NoetherianSpace X := c.i.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact c.i := inferInstance
  -- `R ≅ R_g ⋙ i^*`, since `Rf₀! = Rg_* ∘ i_!` for the compactification defining `Rf₀!`
  have e : derivedLowerShriek k₀ l f ≅ extensionByZero c.i ⋙ derivedLowerStar c.g :=
    NatIso.ofComponents (fun K ↦ Iso.refl _) (fun φ ↦ by
      rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl)
  let eR : R ≅ (derivedLowerStar (k₀ := k₀) (l := l) c.g).rightAdjoint ⋙ upperStar c.i :=
    adj.rightAdjointUniq (((extensionByZeroUpperStarAdjunction c.i).comp adjg).ofNatIsoLeft e.symm)
  -- the underlying complex of `R_g L` is `ḡ^!` of that of `L`
  obtain ⟨eg⟩ := IsoAlgebra.nonempty_forget_obj_iso_of_adjunction
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l c.g (comp_over c.g _))
      (DerivedCategory.boundedConstructibleAdic l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (DerivedCategory.boundedConstructibleAdic l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (fun _ hK ↦ hK.1) (fun K n hK ↦ ObjectProperty.le_shift _ n K hK) hPC_F hPD_G hR
      adjR' hcoprod
      (WeilComplex.objectProperty k₀ l c.Z) (WeilComplex.objectProperty k₀ l _)
      (WeilComplex.objectProperty_iff (X := c.Z)) (WeilComplex.objectProperty_iff (X := _))
      (WeilComplex.objectProperty_rightDerivedLowerStar c.g) adjg L
  obtain ⟨eB⟩ := hR' ⟨_, (WeilComplex.objectProperty_iff _).1 L.property⟩
  -- the chain of isomorphisms (`have` rather than `let`: elaborating the composite with its
  -- type is slow)
  have i₁ := forget.mapIso (eR.app L)
  have i₂ := (upperStarCompForgetIso (k₀ := k₀) (l := l) c.i).app
    ((derivedLowerStar (k₀ := k₀) (l := l) c.g).rightAdjoint.obj L)
  have i₃ := (adicUpperStar l (Scheme.Hom.geometricFiberMap c.i
    (comp_over c.i _))).mapDerivedCategory.mapIso eg
  have i₄ := (adicUpperStarMapDerivedCategoryCompIso l _ (Scheme.Hom.geometricFiberMap c.i
    (comp_over c.i _))).app (R'.obj ⟨_, (WeilComplex.objectProperty_iff _).1 L.property⟩).obj
  have i₅ := (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    cb.overI.left).mapDerivedCategory.mapIso eB
  have i₆ := (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
    (Profinite.padicAlgClRingObj l) cb.overI.left).symm.app
      ((CondensedRing.boundedConstructibleLowerStar l cb.overG).rightAdjoint.obj
        ⟨_, (boundedConstructibleAdic_iff_boundedConstructible l k₀ (AlgebraicClosure k₀)
          (Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure) _).1
          ((objectProperty_iff (X := Y) L.obj).1 L.property)⟩).obj
  have i₇ := (CondensedRing.boundedConstructibleUpperStarCompatibility
    (Profinite.padicAlgClRingObj l) l cb.overI).symm.app
      ((CondensedRing.boundedConstructibleLowerStar l cb.overG).rightAdjoint.obj
        ⟨_, (boundedConstructibleAdic_iff_boundedConstructible l k₀ (AlgebraicClosure k₀)
          (Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure) _).1
          ((objectProperty_iff (X := Y) L.obj).1 L.property)⟩)
  exact ⟨(adicSheafDerivedEquivCondensedMod l _).functor.mapIso (i₁ ≪≫ i₂ ≪≫ i₃) ≪≫ i₄ ≪≫ i₅ ≪≫
    i₆ ≪≫ i₇⟩

/-- **The Weil exceptional inverse image lies over the geometric one** (blueprint
`prose-10-20`): for a separated morphism of finite type `f : X ⟶ Y` of `k₀`-schemes,
a right adjoint `R` of `Rf₀!` on Weil complexes and a Weil complex `L` on `Y`, the underlying
complex of `R L` on `X̄`, in the condensed model, is `Rf̄^!` of the underlying complex of `L`. -/
theorem nonempty_adicSheafDerivedEquivCondensedMod_forget_obj_iso_upperShriek
    {R : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X} (adj : derivedLowerShriek k₀ l f ⊣ R)
    (L : WeilComplex k₀ l Y) :
    Nonempty ((adicSheafDerivedEquivCondensedMod l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.obj (forget.obj (R.obj L)) ≅
      ((CondensedRing.boundedConstructibleUpperShriek l (geometricFiberHom (k₀ := k₀) f)).obj
        (geometricFiberBoundedConstructibleObj L)).obj) := by
  obtain ⟨e⟩ :=
    nonempty_adicSheafDerivedEquivCondensedMod_forget_obj_iso_upperShriekOfCompactification f adj L
  exact ⟨e ≪≫ (ObjectProperty.ι _).mapIso ((conjugateIsoEquiv
    (CondensedRing.boundedConstructibleUpperShriekOfCompactificationAdjunction l
      (geometricFiberHomCompactification (k₀ := k₀) f))
    (CondensedRing.boundedConstructibleUpperShriekAdjunction l (geometricFiberHom (k₀ := k₀) f))
    (CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl l _
      (geometricFiberHomCompactification (k₀ := k₀) f))).app _)⟩

end Relative

/-- **The Weil exceptional inverse image lies over the geometric one.** For a right adjoint `R` of
`Ra_!` on Weil complexes and a Weil complex `L` on `Spec k₀`, the underlying complex of `R L` on
`X̄`, in the condensed model, is `Rā^!(c̄)` of the underlying complex of `L`, for the
compactification `c̄` of `X̄ ⟶ (Spec k₀)̄` obtained by base change. -/
theorem nonempty_adicSheafDerivedEquivCondensedMod_forget_obj_iso_of_adjunction
    {R : WeilComplex k₀ l (Spec (CommRingCat.of k₀)) ⥤ WeilComplex k₀ l X}
    (adj : derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀)) ⊣ R)
    (L : WeilComplex k₀ l (Spec (CommRingCat.of k₀))) :
    Nonempty ((adicSheafDerivedEquivCondensedMod l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.obj (forget.obj (R.obj L)) ≅
      ((CondensedRing.boundedConstructibleUpperShriekOfCompactification l
        (geometricFiberCompactification (k₀ := k₀) X)).obj
          ⟨(adicSheafDerivedEquivCondensedMod l
            (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.obj
              (forget.obj L),
            (boundedConstructibleAdic_iff_boundedConstructible l k₀ (AlgebraicClosure k₀)
              (pointGeometricFiberOver k₀) _).1
              ((objectProperty_iff (X := Spec (CommRingCat.of k₀)) L.obj).1 L.property)⟩).obj) :=
  nonempty_adicSheafDerivedEquivCondensedMod_forget_obj_iso_upperShriekOfCompactification
    (X ↘ Spec (CommRingCat.of k₀)) adj L


instance : IsIso (pointGeometricFiberOver k₀).hom := by
  dsimp only [pointGeometricFiberOver, Over.mk_hom, Scheme.Hom.geometricFiberToAlgebraicClosure]
  infer_instance

variable (k₀ l) in
/-- The underlying complex of the constant Weil sheaf `ℚ̄_ℓ` on `Spec k₀`, in the condensed model,
is the unit `ℚ̄_ℓ` on the geometric fibre. -/
noncomputable def adicSheafDerivedEquivCondensedModForgetConstantIso :
    (adicSheafDerivedEquivCondensedMod l
        (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.obj
        (forget.obj (WeilSheaf.toComplex.obj
          (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀))))) ≅
      𝟙_ (_root_.DerivedCategory (CategoryTheory.Mod
        (Sheaf (Scheme.ProEt.topology
          (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiber) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj l)
          (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiber))) :=
  (adicSheafDerivedEquivCondensedMod l _).functor.mapIso
      (((IsoAlgebra.forget _).mapDerivedCategorySingleFunctor 0).app _) ≪≫
    ((adicSheafEquivCondensedMod l _).functor.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso (adicSheafEquivCondensedModUnitIso l _) ≪≫
    _root_.DerivedCategory.singleFunctorObjUnitIso _

/-- **The underlying complex of the dualizing complex of Weil complexes** (blueprint:
`prose-10-20`): for a right adjoint `R` of the direct image with compact support
`Ra_!` of Weil complexes along the structure morphism `a : X ⟶ Spec k₀`, the underlying complex
on the geometric fibre `X̄` of `R ℚ̄_ℓ` is the dualizing complex `ω_X̄` of `X̄` over `k̄`. -/
theorem nonempty_nativeGeometricForget_obj_iso_of_adjunction
    {R : WeilComplex k₀ l (Spec (CommRingCat.of k₀)) ⥤ WeilComplex k₀ l X}
    (adj : derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀)) ⊣ R) :
    Nonempty ((ProEtaleWeilSheaf.nativeGeometricForget k₀ l X).obj
        (R.obj (WeilSheaf.toComplex.obj
          (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀))))).obj ≅
      (ObjectProperty.ι _).obj (CondensedRing.dualizingComplex l
        (Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure))) := by
  obtain ⟨e₁⟩ := nonempty_adicSheafDerivedEquivCondensedMod_forget_obj_iso_of_adjunction adj
    (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀))))
  obtain ⟨e₂⟩ := CondensedRing.nonempty_upperShriekOfCompactification_obj_unit_iso l
    (f := geometricFiberStructureMorphism (k₀ := k₀) X) (geometricFiberCompactification X)
  exact ⟨(Functor.mapDerivedCategoryNatIso
      (forgetAbCompComapNativeModuleCoefficientIso l _)).app _ ≪≫ e₁ ≪≫
    (ObjectProperty.ι _).mapIso ((CondensedRing.boundedConstructibleUpperShriekOfCompactification l
      (geometricFiberCompactification (k₀ := k₀) X)).mapIso
        (ObjectProperty.isoMk _ (adicSheafDerivedEquivCondensedModForgetConstantIso k₀ l)) ≪≫ e₂)⟩
end WeilComplex

end AlgebraicGeometry
