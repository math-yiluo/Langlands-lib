/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.EtaleCohomologyComparison
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj
public import WeilConjectures.Mathlib.Algebra.Group.Equiv.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import WeilConjectures.SixFunctors.Etale.ConstantCohomologyExtPullback
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicEtale

/-!
# The explicit comparison of `Hⁿ(S_proét, ℤ/ℓᵐ)` with `Hom(Λ_S, Λ_S[n])`

For a quasi-compact quasi-separated scheme `S` and `Λ = ℤ/ℓᵐ`, the chain of comparisons
`Hom_{D(S_ét, Λ)}(Λ_S, Λ_S[n]) ≅ Extⁿ_Λ(Λ_S, Λ_S) ≅ Hⁿ(S_ét, Λ) ≅ Hⁿ(S_proét, ν^* Λ)
≅ Hⁿ(S_proét, C(-, ℤ_ℓ/ℓᵐ))` is given by explicit additive equivalences
(`AlgebraicGeometry.ProEtale.extAddEquivFiniteAdicH`,
`AlgebraicGeometry.ProEtale.unitShiftAddEquivFiniteAdicH`), making
`AlgebraicGeometry.ProEtale.nonempty_addEquiv_finiteAdicH_unitShift` explicit. The composite
`Extⁿ_Λ(Λ_S, Λ_S) ≅ Hⁿ(S_proét, C(-, ℤ_ℓ/ℓᵐ))` is the pushforward of `Ext`-classes along the exact
functor `ν^* ∘ forget` composed with explicit morphisms on both sides
(`AlgebraicGeometry.ProEtale.extAddEquivFiniteAdicH_apply`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

/-! Without this, `ModuleCat (ULift (ZMod (l ^ m)))` elaborates with the ring structure
`ULift.ring`, while the constructions on sheaves of modules over a commutative ring use
`CommRing.toRing`; the kernel then has to unfold the sheaf categories to compare the two. -/
attribute [local instance 2000] CommRing.toRing

namespace CategoryTheory.Abelian.Ext

/-- `y ↦ a ∘ G(y) ∘ b` for an exact functor `G`, as an additive map. -/
noncomputable def mk₀CompMk₀MapExactFunctorAddHom {C : Type*} [Category C] [Abelian C]
    [HasExt.{u} C] {D : Type*} [Category D] [Abelian D] [HasExt.{u} D] (G : C ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] {X Y : C} {X' Y' : D}
    (a : X' ⟶ G.obj X) (b : G.obj Y ⟶ Y') (n : ℕ) : Ext X Y n →+ Ext X' Y' n :=
  AddMonoidHom.mk' (fun y ↦ mk₀CompMk₀ a (y.mapExactFunctor G) b) fun y y' ↦ by
    rw [mapExactFunctor_add, mk₀CompMk₀_add]

end CategoryTheory.Abelian.Ext

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category C] {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]

/-- The additive equivalence of cohomology groups induced by an isomorphism of sheaves. -/
noncomputable def H.mapAddEquiv {F G : Sheaf J AddCommGrpCat.{u}} (e : F ≅ G) (n : ℕ) :
    H F n ≃+ H G n :=
  Ext.postcompAddEquiv _ e n

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.ProEtale

open Scheme

section Instances

/-! The `HasExt` instances of the sheaf categories used below, as lemmas applied to variables,
used as local instances. Instance synthesis otherwise produces `IsGrothendieckAbelian.hasExt`
applied to the (non-atomic) sheaf category; inside definitions this proof is abstracted into an
auxiliary lemma stating the unfolded `HasExt`, which the kernel can only compare with the original
by unfolding the derived category constructions. -/

/-- `HasExt` for étale sheaves of `ℤ/ℓᵐ`-modules, as a lemma to be used as a local instance. -/
lemma hasExt_sheafEtaleModuleCatZMod (l m : ℕ) (S : Scheme.{u}) :
    HasExt.{u + 1}
      (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (l ^ m))))) :=
  inferInstance

/-- `HasExt` for abelian étale sheaves, as a lemma to be used as a local instance. -/
lemma hasExt_sheafEtaleAddCommGrpCat (S : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  inferInstance

/-- `HasExt` for abelian pro-étale sheaves, as a lemma to be used as a local instance. -/
lemma hasExt_sheafProEtAddCommGrpCat (S : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1}) :=
  inferInstance

end Instances

attribute [local instance high] hasExt_sheafEtaleModuleCatZMod hasExt_sheafEtaleAddCommGrpCat
  hasExt_sheafProEtAddCommGrpCat

/-! The constructions on sheaves of modules over a commutative ring `Λ` (such as
`AlgebraicGeometry.Etale.upperStarConstantRingIso`) sheafify through `HasSheafify`; for
`Λ = ULift (ZMod (l ^ m))`, instance synthesis would otherwise use the concrete sheafification
`CategoryTheory.sheafToPresheaf_isRightAdjoint` in `Sheaf.constantRing`, and the kernel would
have to unfold the sheaf categories to compare the two. -/
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint

variable (l : ℕ) [Fact l.Prime] (m : ℕ) (S : Scheme.{u})

/-- The coefficients `ℤ/ℓᵐ ≅ ℤ_ℓ/ℓᵐ`, as abelian groups. -/
noncomputable def zmodIsoQuotientPowOpenAddSubgroup :
    AddCommGrpCat.of (ULift.{u + 1} (ZMod (l ^ m))) ≅
      AddCommGrpCat.of
        (ULift.{u + 1} (ℤ_[l] ⧸ (PadicInt.powOpenAddSubgroup l m : AddSubgroup ℤ_[l]))) :=
  (AddEquiv.ulift.trans ((zmodAddEquivQuotientPowOpenAddSubgroup l m).trans
    AddEquiv.ulift.symm)).toAddCommGrpIso

/-- The underlying abelian sheaf of the constant étale sheaf `ℤ/ℓᵐ` is the constant abelian
sheaf `ℤ_ℓ/ℓᵐ`. -/
noncomputable def sheafForget₂ConstantRingIsoQuotient :
    (Etale.sheafForget₂ (ULift.{u + 1} (ZMod (l ^ m))) S).obj
        (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m)))) ≅
      (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of
          (ULift.{u + 1} (ℤ_[l] ⧸ (PadicInt.powOpenAddSubgroup l m : AddSubgroup ℤ_[l])))) :=
  Etale.sheafForget₂ConstantRingIso (ULift.{u + 1} (ZMod (l ^ m))) S ≪≫
    (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso
      (zmodIsoQuotientPowOpenAddSubgroup l m)

/-- The exact functor `ν^* ∘ forget` from étale sheaves of `ℤ/ℓᵐ`-modules to abelian
pro-étale sheaves. -/
noncomputable abbrev forgetComparisonUpperStar :
    Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (l ^ m)))) ⥤
      Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1} :=
  Etale.sheafForget₂ (ULift.{u + 1} (ZMod (l ^ m))) S ⋙
    comparisonUpperStar AddCommGrpCat.{u + 1} S

/-- `ν^*` of the underlying abelian sheaf of `ℤ/ℓᵐ` is `C(-, ℤ_ℓ/ℓᵐ)`. -/
noncomputable def forgetComparisonUpperStarConstantRingIso :
    (forgetComparisonUpperStar l m S).obj
        (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m)))) ≅
      continuousSheaf S (ℤ_[l] ⧸ (PadicInt.powOpenAddSubgroup l m : AddSubgroup ℤ_[l])) :=
  (comparisonUpperStar AddCommGrpCat.{u + 1} S).mapIso
      (sheafForget₂ConstantRingIsoQuotient l m S) ≪≫
    (comparisonUpperStarConstantSheafIsoAddCommGrpCat S).app _ ≪≫
      constantSheafIsoContinuousSheaf S _

/-- The class `ℤ ⟶ ν^* Λ` of the section `1`. -/
noncomputable def forgetComparisonUpperStarUnit :
    (constantSheaf (ProEt.topology S) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      (forgetComparisonUpperStar l m S).obj
        (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m)))) :=
  (constantIntIsoComparisonUpperStar S).hom ≫ (comparisonUpperStar AddCommGrpCat.{u + 1} S).map
    (Sheaf.constantIntToRing S.smallEtaleTopology (Etale.terminalEtaleIsTerminal S)
      (ULift.{u + 1} (ZMod (l ^ m))))

variable [CompactSpace S] [QuasiSeparatedSpace S]

/-- `y ↦ u ∘ (ν^* ∘ forget)(y) ∘ v` is the composite of the comparison of `Ext` over `Λ` with
abelian étale cohomology, of the coefficients, and of étale with pro-étale cohomology; in
particular it is bijective. -/
lemma bijective_mk₀CompMk₀AddHom_forgetComparisonUpperStar (n : ℕ) :
    Function.Bijective (Ext.mk₀CompMk₀MapExactFunctorAddHom (forgetComparisonUpperStar l m S)
      (forgetComparisonUpperStarUnit l m S)
      (forgetComparisonUpperStarConstantRingIso l m S).hom n) := by
  have h : ⇑(Ext.mk₀CompMk₀MapExactFunctorAddHom (forgetComparisonUpperStar l m S)
      (forgetComparisonUpperStarUnit l m S)
      (forgetComparisonUpperStarConstantRingIso l m S).hom n) =
      ⇑(Ext.postcompAddEquiv (Y := (comparisonUpperStar AddCommGrpCat.{u + 1} S).obj
          ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of
            (ULift.{u + 1} (ℤ_[l] ⧸ (PadicInt.powOpenAddSubgroup l m : AddSubgroup ℤ_[l]))))))
          _ ((comparisonUpperStarConstantSheafIsoAddCommGrpCat S).app _ ≪≫
            constantSheafIsoContinuousSheaf S _) n) ∘
        ⇑(cohomologyComparison S _ n) ∘
        ⇑(Ext.postcompAddEquiv _ (sheafForget₂ConstantRingIsoQuotient l m S) n) ∘
        ⇑((Etale.sheafForget₂ (ULift.{u + 1} (ZMod (l ^ m))) S).mapExtComp
          (Sheaf.constantIntToRing S.smallEtaleTopology (Etale.terminalEtaleIsTerminal S)
            (ULift.{u + 1} (ZMod (l ^ m)))) _ n) := by
    funext y
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply,
      Ext.postcompAddEquiv_apply, Ext.postcompAddEquiv_apply, Functor.mapExtComp_apply,
      Ext.mk₀_comp_comp_mk₀, cohomologyComparison_apply, Ext.mapExactFunctor_mk₀CompMk₀,
      Ext.mk₀_comp_mk₀CompMk₀, Ext.mk₀CompMk₀_comp_mk₀, Ext.mapExactFunctor_mapExactFunctor]
    rfl
  rw [h]
  exact (AddEquiv.bijective _).comp ((bijective_cohomologyComparison S _ n).comp
    ((AddEquiv.bijective _).comp
      (Etale.bijective_mapExtComp_constantIntToRing (ULift.{u + 1} (ZMod (l ^ m))) S _ n)))

/-- **`Extⁿ_Λ(Λ_S, Λ_S)` is `Hⁿ(S_proét, ℤ_ℓ/ℓᵐ)`**, `Λ = ℤ/ℓᵐ`: the map
`y ↦ u ∘ (ν^* ∘ forget)(y) ∘ v`, which is the composite of the comparison of `Ext` over `Λ` with
abelian étale cohomology, of the coefficients, and of étale with pro-étale cohomology. -/
noncomputable def extAddEquivFiniteAdicH (n : ℕ) :
    Ext (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m))))
        (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m)))) n ≃+
      FiniteAdicH S l m n :=
  AddEquiv.ofBijectiveAddMonoidHom _
    (bijective_mk₀CompMk₀AddHom_forgetComparisonUpperStar l m S n)

/-- The comparison `Extⁿ_Λ(Λ_S, Λ_S) ≅ Hⁿ(S_proét, ℤ_ℓ/ℓᵐ)` is `y ↦ u ∘ (ν^* ∘ forget)(y) ∘ v`. -/
lemma extAddEquivFiniteAdicH_apply (n : ℕ)
    (y : Ext (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m))))
      (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m)))) n) :
    extAddEquivFiniteAdicH l m S n y =
      Ext.mk₀CompMk₀ (forgetComparisonUpperStarUnit l m S)
        (y.mapExactFunctor (forgetComparisonUpperStar l m S))
        (forgetComparisonUpperStarConstantRingIso l m S).hom :=
  rfl

end AlgebraicGeometry.ProEtale
