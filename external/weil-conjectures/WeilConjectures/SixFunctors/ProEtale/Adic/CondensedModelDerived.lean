/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelEquivalenceFunctoriality
public import WeilConjectures.SixFunctors.ProEtale.Adic.DerivedGlobalSectionsTransport
public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek

/-!
# The two models of `ℓ`-adic complexes agree

Let `E_X := AlgebraicGeometry.ProEtale.adicSheafEquivCondensedMod ℓ X` be the equivalence between
`ℓ`-adic sheaves (sheaves of `ℚ̄_ℓ,X`-modules) and module objects over the condensed coefficient
ring `Λ_X = p_X^* ℚ̄_ℓ` in abelian sheaves on `X_proét`. Being an exact equivalence, it induces an
equivalence of unbounded derived categories `D(E_X)`, commuting with shifts, cohomology sheaves
and the embeddings in a single degree. The compatibilities of `E` with pushforward, pullback and
extension by zero pass to the derived functors:

- derived pullback: both pullbacks are exact and `D(f^*) ⋙ D(E_Y) ≅ D(E_X) ⋙ D(f^*)`;
- derived pushforward: `Rf_* ⋙ D(E_X) ≅ D(E_Y) ⋙ Rf_*`. The right derived functors are
  computed by K-injective resolutions; an equivalence preserves K-injective complexes (it is a
  right adjoint of its exact inverse), so `R(f_* ⋙ E_X) ≅ Rf_* ⋙ D(E_X)` and
  `R(E_Y ⋙ f_*) ≅ D(E_Y) ⋙ Rf_*`;
- extension by zero along an open immersion `j`: both `j_!` are left adjoint to the pullbacks,
  so `j_! ⋙ E_X ≅ E_U ⋙ j_!` is the conjugate of the pullback compatibility; both are exact;
- hence the derived lower shriek `Rf_! = Rg_* ∘ D(i_!)` attached to a compactification
  `Y ⟶[i] Z ⟶[g] X`, which is literally how both models define it, and the compactly supported
  derived global sections (as complexes of abelian groups).

## Main results

- `CategoryTheory.Adjunction.leftAdjointCompIsoOfEquivalence`: transport of left adjoints along
  equivalences.
- `CategoryTheory.Functor.rightDerivedFunctorCompMapDerivedCategoryIsoOfEquivalence`: transport of
  right derived functors along equivalences of abelian categories.
- `AlgebraicGeometry.ProEtale.adicSheafDerivedEquivCondensedMod`: the derived equivalence
  `D(AdicSheaf ℓ X) ≌ D(Mod_{Λ_X})`.
- `AlgebraicGeometry.ProEtale.adicRightDerivedLowerStarCompIso`: `Rf_* ⋙ D(E_X) ≅ D(E_Y) ⋙ Rf_*`.
- `AlgebraicGeometry.ProEtale.adicOpenImmersionLowerShriekCompCondensedModIso`:
  `j_! ⋙ E_X ≅ E_U ⋙ j_!`.
- `AlgebraicGeometry.ProEtale.adicRightDerivedLowerShriekCompIso`: `Rf_! ⋙ D(E_X) ≅ D(E_Y) ⋙ Rf_!`
  for the chosen compactification, the new `Rf_!` being
  `AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriek`.
- `AlgebraicGeometry.ProEtale.adicCompactlySupportedGlobalSectionsCompForgetIso`: the compactly
  supported derived global sections of the two models agree as complexes of abelian groups.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits
open scoped Obj

namespace CategoryTheory

attribute [local instance] Limits.comp_preservesFiniteLimits Limits.comp_preservesFiniteColimits

section Abstract

variable {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]

/-- An isomorphism `R ⋙ E₂ ≅ E₁ ⋙ R'` intertwining two functors along equivalences `E₁`, `E₂`
gives the isomorphism `E₁⁻¹ ⋙ R ≅ R' ⋙ E₂⁻¹` for the quasi-inverses. -/
noncomputable def Equivalence.inverseCompIsoCompInverse (E₁ : C₁ ≌ D₁) (E₂ : C₂ ≌ D₂)
    {R : C₁ ⥤ C₂} {R' : D₁ ⥤ D₂} (e : R ⋙ E₂.functor ≅ E₁.functor ⋙ R') :
    E₁.inverse ⋙ R ≅ R' ⋙ E₂.inverse :=
  Iso.inverseCompIso (Iso.isoCompInverse e ≪≫ Functor.associator _ _ _)

/-- **Transport of left adjoints along equivalences**: if `L ⊣ R` and `L' ⊣ R'`, an isomorphism
`R ⋙ E₂ ≅ E₁ ⋙ R'` intertwining the right adjoints along equivalences `E₁ : C₁ ≌ D₁`,
`E₂ : C₂ ≌ D₂` induces the conjugate isomorphism `L ⋙ E₁ ≅ E₂ ⋙ L'` of the left adjoints. -/
noncomputable def Adjunction.leftAdjointCompIsoOfEquivalence {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂}
    {L' : D₂ ⥤ D₁} {R' : D₁ ⥤ D₂} (adj : L ⊣ R) (adj' : L' ⊣ R') (E₁ : C₁ ≌ D₁) (E₂ : C₂ ≌ D₂)
    (e : R ⋙ E₂.functor ≅ E₁.functor ⋙ R') :
    L ⋙ E₁.functor ≅ E₂.functor ⋙ L' :=
  ((conjugateIsoEquiv (adj.comp E₁.toAdjunction) (E₂.toAdjunction.comp adj')).symm
    (E₁.inverseCompIsoCompInverse E₂ e)).symm

end Abstract

section Derived

open Abelian

variable {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
  [Abelian C₁] [Abelian C₂] [Abelian D₁] [Abelian D₂]

/-- An equivalence of abelian categories preserves K-injective complexes: its functor is right
adjoint to its (exact) inverse. -/
lemma Equivalence.preservesKInjectiveComplexes_functor (E : C₁ ≌ D₁) [E.functor.Additive] :
    E.functor.PreservesKInjectiveComplexes :=
  Adjunction.preservesKInjectiveComplexes (G := E.inverse) (F := E.functor) E.symm.toAdjunction

variable [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory D₁]
  [HasDerivedCategory D₂]

/-- **Exact functors intertwined along exact functors**: an isomorphism `F ⋙ G ≅ G' ⋙ F'` of
exact functors `C₁ ⥤ D₂` induces `D(F) ⋙ D(G) ≅ D(G') ⋙ D(F')` on derived categories. -/
noncomputable def Functor.mapDerivedCategoryCompIsoOfIso {F : C₁ ⥤ C₂} {G : C₂ ⥤ D₂}
    {G' : C₁ ⥤ D₁} {F' : D₁ ⥤ D₂} [F.Additive] [G.Additive] [G'.Additive] [F'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F'] (e : F ⋙ G ≅ G' ⋙ F') :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      G'.mapDerivedCategory ⋙ F'.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F G) ≪≫ Functor.mapDerivedCategoryNatIso e ≪≫
    (Functor.mapDerivedCategoryCompIso G' F').symm

/-- **Right derived functors along equivalences**: if `E₁ : C₁ ≌ D₁` and `E₂ : C₂ ≌ D₂` are
equivalences of abelian categories and `e : F ⋙ E₂ ≅ E₁ ⋙ F'` intertwines additive functors
`F : C₁ ⥤ C₂` and `F' : D₁ ⥤ D₂`, then the total right derived functors are intertwined by the
induced equivalences of derived categories: `RF ⋙ D(E₂) ≅ D(E₁) ⋙ RF'`. -/
noncomputable def Functor.rightDerivedFunctorCompMapDerivedCategoryIsoOfEquivalence
    [HasKInjectiveResolutions C₁] [HasKInjectiveResolutions D₁]
    (E₁ : C₁ ≌ D₁) (E₂ : C₂ ≌ D₂) [E₁.functor.Additive] [E₂.functor.Additive]
    {F : C₁ ⥤ C₂} {F' : D₁ ⥤ D₂} [F.Additive] [F'.Additive]
    (e : F ⋙ E₂.functor ≅ E₁.functor ⋙ F') :
    F.rightDerivedFunctor ⋙ E₂.functor.mapDerivedCategory ≅
      E₁.functor.mapDerivedCategory ⋙ F'.rightDerivedFunctor :=
  have := E₁.preservesKInjectiveComplexes_functor
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F E₂.functor).symm ≪≫
    Functor.rightDerivedFunctorIsoMapDerivedCategoryComp e.symm

end Derived

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

instance : (adicSheafEquivCondensedMod l X).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-! ### The derived equivalence -/

/-- **The two models of `ℓ`-adic complexes agree**: the equivalence
`AlgebraicGeometry.ProEtale.adicSheafEquivCondensedMod` of abelian categories induces an
equivalence `D(AdicSheaf ℓ X) ≌ D(Mod_{Λ_X})` of unbounded derived categories, with functor
`D(E_X)` (applying `E_X` degreewise) and inverse `D(E_X⁻¹)`. -/
noncomputable def adicSheafDerivedEquivCondensedMod :
    _root_.DerivedCategory (AdicSheaf l X) ≌
      _root_.DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj l) X)) :=
  (adicSheafEquivCondensedMod l X).mapDerivedCategory

lemma adicSheafDerivedEquivCondensedMod_functor :
    (adicSheafDerivedEquivCondensedMod l X).functor =
      (adicSheafEquivCondensedMod l X).functor.mapDerivedCategory :=
  rfl

lemma adicSheafDerivedEquivCondensedMod_inverse :
    (adicSheafDerivedEquivCondensedMod l X).inverse =
      (adicSheafEquivCondensedMod l X).inverse.mapDerivedCategory :=
  rfl

/-- The derived comparison commutes with the shifts. -/
noncomputable instance : (adicSheafDerivedEquivCondensedMod l X).functor.CommShift ℤ :=
  inferInstanceAs ((adicSheafEquivCondensedMod l X).functor.mapDerivedCategory.CommShift ℤ)

/-- The derived comparison is a triangulated functor. -/
instance : (adicSheafDerivedEquivCondensedMod l X).functor.IsTriangulated :=
  inferInstanceAs ((adicSheafEquivCondensedMod l X).functor.mapDerivedCategory.IsTriangulated)

/-- The derived comparison commutes with the cohomology sheaves:
`E_X (Hⁿ K) ≅ Hⁿ (D(E_X) K)`. -/
noncomputable def homologyFunctorCompAdicSheafEquivCondensedModIso (n : ℤ) :
    _root_.DerivedCategory.homologyFunctor (AdicSheaf l X) n ⋙
        (adicSheafEquivCondensedMod l X).functor ≅
      (adicSheafDerivedEquivCondensedMod l X).functor ⋙
        _root_.DerivedCategory.homologyFunctor _ n :=
  Functor.mapDerivedCategoryHomologyFunctorIso _ n

/-- The derived comparison commutes with the embeddings of the abelian categories in degree
`n`: `D(E_X) (M[-n]) ≅ (E_X M)[-n]`. -/
noncomputable def singleFunctorCompAdicSheafDerivedEquivCondensedModIso (n : ℤ) :
    _root_.DerivedCategory.singleFunctor (AdicSheaf l X) n ⋙
        (adicSheafDerivedEquivCondensedMod l X).functor ≅
      (adicSheafEquivCondensedMod l X).functor ⋙ _root_.DerivedCategory.singleFunctor _ n :=
  Functor.mapDerivedCategorySingleFunctor _ n

/-! ### Derived pullback -/

/-- **Derived pullback compatibility of the two models**: both pullbacks are exact, and the
derived comparisons intertwine the induced functors: `D(f^*) ⋙ D(E_Y) ≅ D(E_X) ⋙ D(f^*)`,
from the underived compatibility `AlgebraicGeometry.ProEtale.adicUpperStarCompCondensedModIso`. -/
noncomputable def adicUpperStarMapDerivedCategoryCompIso {Y : Scheme.{u}} (f : Y ⟶ X) :
    (f)^*ᵃ[l].mapDerivedCategory ⋙ (adicSheafDerivedEquivCondensedMod l Y).functor ≅
      (adicSheafDerivedEquivCondensedMod l X).functor ⋙
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIsoOfIso (adicUpperStarCompCondensedModIso l f)

/-! ### Derived pushforward -/

/-- **Derived pushforward compatibility of the two models**: the derived comparisons intertwine
the total right derived pushforward of sheaves of `ℚ̄_ℓ`-modules with that of module objects over
`Λ = p^* ℚ̄_ℓ`: `Rf_* ⋙ D(E_X) ≅ D(E_Y) ⋙ Rf_*`. It is obtained from the underived compatibility
`AlgebraicGeometry.ProEtale.adicLowerStarCompCondensedModIso` by
`CategoryTheory.Functor.rightDerivedFunctorCompMapDerivedCategoryIsoOfEquivalence`. -/
noncomputable def adicRightDerivedLowerStarCompIso {Y : Scheme.{u}} (f : Y ⟶ X) :
    (f)_*ᵃ[l].rightDerivedFunctor ⋙ (adicSheafDerivedEquivCondensedMod l X).functor ≅
      (adicSheafDerivedEquivCondensedMod l Y).functor ⋙
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).rightDerivedFunctor :=
  Functor.rightDerivedFunctorCompMapDerivedCategoryIsoOfEquivalence _ _
    (adicLowerStarCompCondensedModIso l f)

/-! ### Extension by zero -/

/-- **Extension by zero compatibility of the two models**: for an open immersion `j : U ⟶ X`,
the comparison intertwines the extension by zero `j_!` of sheaves of `ℚ̄_ℓ,U`-modules with the
extension by zero of module objects over `Λ_U`: `j_! ⋙ E_X ≅ E_U ⋙ j_!`. Both are left adjoint to
the pullbacks `j^*`, so this is the conjugate of the pullback compatibility
`AlgebraicGeometry.ProEtale.adicUpperStarCompCondensedModIso`. -/
noncomputable def adicOpenImmersionLowerShriekCompCondensedModIso {U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    (j)_!ᵃ[l] ⋙ (adicSheafEquivCondensedMod l X).functor ≅
      (adicSheafEquivCondensedMod l U).functor ⋙
        CondensedRing.openImmersionLowerShriek (Profinite.padicAlgClRingObj l) j :=
  Adjunction.leftAdjointCompIsoOfEquivalence (adicOpenImmersionLowerShriekAdjunction l j)
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction _ j) _ _
    (adicUpperStarCompCondensedModIso l j)

/-- The extension by zero compatibility on derived categories:
`D(j_!) ⋙ D(E_X) ≅ D(E_U) ⋙ D(j_!)`, both extensions by zero being exact. -/
noncomputable def adicOpenImmersionLowerShriekMapDerivedCategoryCompIso {U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (j)_!ᵃ[l].mapDerivedCategory ⋙ (adicSheafDerivedEquivCondensedMod l X).functor ≅
      (adicSheafDerivedEquivCondensedMod l U).functor ⋙
        (CondensedRing.openImmersionLowerShriek (Profinite.padicAlgClRingObj l)
          j).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIsoOfIso (adicOpenImmersionLowerShriekCompCondensedModIso l X j)

/-! ### Derived lower shriek -/

/-- **Derived lower shriek compatibility of the two models**, for a compactification
`c = (Y ⟶[i] Z ⟶[g] X)` of `f : Y ⟶ X`: the old-model direct image with compact support
`Rf_! = Rg_* ∘ D(i_!)` (as in
`AlgebraicGeometry.ProEtale.algClosedCompactlySupportedGlobalSections`)
is intertwined by the derived comparisons with the new-model
`AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification`. -/
noncomputable def adicRightDerivedLowerShriekOfCompactificationCompIso {Y : Scheme.{u}}
    {f : Y ⟶ X} (c : Compactification f) :
    ((c.i)_!ᵃ[l].mapDerivedCategory ⋙ (c.g)_*ᵃ[l].rightDerivedFunctor) ⋙
        (adicSheafDerivedEquivCondensedMod l X).functor ≅
      (adicSheafDerivedEquivCondensedMod l Y).functor ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification
          (Profinite.padicAlgClRingObj l) c :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (adicRightDerivedLowerStarCompIso l X c.g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (adicOpenImmersionLowerShriekMapDerivedCategoryCompIso l c.Z c.i) _ ≪≫
    Functor.associator _ _ _

/-- **Derived lower shriek compatibility of the two models**, for the chosen compactification:
`Rf_! ⋙ D(E_X) ≅ D(E_Y) ⋙ Rf_!`, where the old `Rf_!` is `Rḡ_* ∘ D(ī_!)` for the chosen
compactification `Y ⟶[ī] Z ⟶[ḡ] X` and the new one is
`AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriek`. -/
noncomputable def adicRightDerivedLowerShriekCompIso {Y : Scheme.{u}} (f : Y ⟶ X)
    [HasCompactification f] :
    (((HasCompactification.compactification f).i)_!ᵃ[l].mapDerivedCategory ⋙
        ((HasCompactification.compactification f).g)_*ᵃ[l].rightDerivedFunctor) ⋙
        (adicSheafDerivedEquivCondensedMod l X).functor ≅
      (adicSheafDerivedEquivCondensedMod l Y).functor ⋙
        CondensedRing.rightDerivedLowerShriek (Profinite.padicAlgClRingObj l) f :=
  adicRightDerivedLowerShriekOfCompactificationCompIso l X _

/-! ### Derived global sections and compactly supported cohomology -/

variable (s : Scheme.{u})

instance : PreservesFiniteLimits (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1}) where
  preservesFiniteLimits _ := ⟨fun {_} ↦ inferInstance⟩

instance : PreservesFiniteColimits (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1}) where
  preservesFiniteColimits _ := ⟨fun {_} ↦ inferInstance⟩

/-- The global sections of an `ℓ`-adic sheaf, as an abelian group, are the global sections of the
underlying abelian sheaf of the corresponding module object over `Λ_s`. -/
noncomputable def condensedModGlobalSectionsIso :
    (adicSheafEquivCondensedMod l s).functor ⋙
        (Mod.forget (condensedRingObj (Profinite.padicAlgClRingObj l) s) ⋙
          Sheaf.Γ (Scheme.ProEt.topology s) Ab.{u + 1}) ≅
      adicGlobalSections l s ⋙ forget₂ (WeilCoefficients.{u} l) Ab.{u + 1} :=
  Iso.refl (AdicSheaf.forget s ⋙ weilCoefficientsForgetAb l s ⋙
      Sheaf.Γ (Scheme.ProEt.topology s) Ab.{u + 1}) ≪≫
    Functor.isoWhiskerLeft (AdicSheaf.forget s) (globalSectionsForgetAbIso l s).symm ≪≫
    (Functor.associator _ _ _).symm

/-- **Derived global sections compatibility of the two models**: the derived global sections
`RΓ(s, -)` of `ℓ`-adic complexes, as complexes of abelian groups, agree with the derived global
sections of the underlying abelian sheaves of the corresponding module objects over `Λ_s`. -/
noncomputable def adicRightDerivedGlobalSectionsCompForgetIso :
    (adicGlobalSections l s).rightDerivedFunctor ⋙
        (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1}).mapDerivedCategory ≅
      (adicSheafDerivedEquivCondensedMod l s).functor ⋙
        (Mod.forget (condensedRingObj (Profinite.padicAlgClRingObj l) s) ⋙
          Sheaf.Γ (Scheme.ProEt.topology s) Ab.{u + 1}).rightDerivedFunctor :=
  have := (adicSheafEquivCondensedMod l s).preservesKInjectiveComplexes_functor
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _).symm ≪≫
    Functor.rightDerivedFunctorIsoMapDerivedCategoryComp (condensedModGlobalSectionsIso l s)

/-- **Compactly supported cohomology in the two models**: for a compactification
`c = (Y ⟶[i] Z ⟶[g] s)` of `a : Y ⟶ s`, the compactly supported derived global sections
`RΓ_c(Y, -) = RΓ(s, -) ∘ Rg_* ∘ D(i_!)` of `ℓ`-adic complexes (the body of
`AlgebraicGeometry.ProEtale.algClosedCompactlySupportedGlobalSections` for the chosen
compactification), as complexes of abelian groups, agree with
`RΓ(s, -) ∘ Rf_!(c)` on module objects over `Λ`. -/
noncomputable def adicCompactlySupportedGlobalSectionsCompForgetIso {Y : Scheme.{u}}
    {a : Y ⟶ s} (c : Compactification a) :
    ((c.i)_!ᵃ[l].mapDerivedCategory ⋙ (c.g)_*ᵃ[l].rightDerivedFunctor ⋙
        (adicGlobalSections l s).rightDerivedFunctor) ⋙
        (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1}).mapDerivedCategory ≅
      (adicSheafDerivedEquivCondensedMod l Y).functor ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification
          (Profinite.padicAlgClRingObj l) c ⋙
        (Mod.forget (condensedRingObj (Profinite.padicAlgClRingObj l) s) ⋙
          Sheaf.Γ (Scheme.ProEt.topology s) Ab.{u + 1}).rightDerivedFunctor :=
  Functor.isoWhiskerRight (Functor.associator _ _ _).symm _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (adicRightDerivedGlobalSectionsCompForgetIso l s) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (adicRightDerivedLowerShriekOfCompactificationCompIso l s c) _ ≪≫
    Functor.associator _ _ _

end AlgebraicGeometry.ProEtale
