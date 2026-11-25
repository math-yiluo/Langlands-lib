/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelEquivalence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

import all WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback

/-!
# Functoriality of the comparison of the two models of `ℓ`-adic sheaves

Let `f : Y ⟶ X` be a morphism of schemes. The equivalence
`AlgebraicGeometry.ProEtale.adicSheafEquivCondensedMod` between `ℓ`-adic sheaves (sheaves of
`ℚ̄_ℓ,X`-modules) and module objects over the condensed coefficient ring `Λ_X = p_X^* ℚ̄_ℓ` in
abelian sheaves is compatible with the pushforward and the pullback along `f` on both sides.

## Pushforward

Both pushforwards are computed on sections by `U ↦ M(U ×_X Y)`: the old one is the pushforward
of sheaves of `ℚ̄_ℓ`-modules, with `ℚ̄_ℓ,X` acting through precomposition
`ℚ̄_ℓ,X ⟶ f_* ℚ̄_ℓ,Y` with the projections, and the new one is the pushforward of abelian
sheaves, with `Λ_X` acting through the canonical coefficient morphism `η_f : Λ_X ⟶ f_* Λ_Y`.
The equivalence keeps the underlying abelian sheaf and transports the action along the
isomorphism of ring objects `Λ_X ≅ forgetAb ℚ̄_ℓ,X`
(`AlgebraicGeometry.ProEtale.condensedRingObjIsoForgetAb`). The two actions agree because this
isomorphism intertwines `η_f` with the precomposition `ℚ̄_ℓ,X ⟶ f_* ℚ̄_ℓ,Y`
(`AlgebraicGeometry.ProEtale.condensedPushforwardHom_comp_map_condensedRingObjIsoForgetAb_hom`):
on sections of `Λ_X` coming from profinite test objects both are precomposition with the
projections, which is the content of the comparison of `η_f` with the bounded coefficient
sheaves in `WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback`; and on the bounded
functions, the comparison `padicAlgClSheaf ≅ forgetAb ℚ̄_ℓ` is the inclusion, which commutes
with precomposition.

## Pullback

The pullbacks are left adjoint to the pushforwards on both sides, so the compatibility of the
pullbacks is the conjugate of the compatibility of the pushforwards (`conjugateIsoEquiv`),
transported through the two equivalences. Taking underlying abelian sheaves and global sections
over `Y`, the global sections of the old pullback `f^* F` agree with those of the new pullback;
for a geometric point `s : Spec Ω ⟶ X` these are the stalks `Γ(Spec Ω, s^* F)` of
`AlgebraicGeometry.WeilSheaf.stalkObj`.

## Main results

- `AlgebraicGeometry.ProEtale.condensedPushforwardHom_comp_map_condensedRingObjIsoForgetAb_hom`:
  `Λ_X ≅ forgetAb ℚ̄_ℓ,X` intertwines `η_f` and `ℚ̄_ℓ,X ⟶ f_* ℚ̄_ℓ,Y`.
- `AlgebraicGeometry.ProEtale.adicLowerStarCompCondensedModIso`: the natural isomorphism
  `f_* ⋙ E_X ≅ E_Y ⋙ f_*`, with identity underlying morphisms
  (`AlgebraicGeometry.ProEtale.adicLowerStarCompCondensedModIso_hom_app_hom`).
- `AlgebraicGeometry.ProEtale.adicUpperStarCompCondensedModIso`: the natural isomorphism
  `f^* ⋙ E_Y ≅ E_X ⋙ f^*`.
- `AlgebraicGeometry.ProEtale.globalSectionsAdicUpperStarIso`: the global sections of the
  underlying abelian sheaves of the two pullbacks agree, and
  `AlgebraicGeometry.ProEtale.globalSectionsAdicUpperStarObjIso` is its component at an
  `ℓ`-adic sheaf, in the form of `AlgebraicGeometry.WeilSheaf.stalkObj`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite
open scoped Obj

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {X Y : Scheme.{u}}

/-! ### Compatibility of the coefficient isomorphisms with the pushforward -/

variable (l X) in
/-- The comparison `padicAlgClSheaf X ℓ ⟶ forgetAb ℚ̄_ℓ,X`, restricted along the unit of
sheafification, is the inclusion of the functions with values in a finite subextension into the
locally finite functions. -/
lemma toSheafify_comp_padicAlgClSheafToAdicConstantSheaf :
    toSheafify (Scheme.ProEt.topology X) (padicAlgClRingPresheaf X l ⋙ forget₂ RingCat Ab) ≫
      (padicAlgClSheafToAdicConstantSheaf X l).hom = padicAlgClPresheafToAdicConstantSheaf X l :=
  ((sheafificationAdjunction (Scheme.ProEt.topology X) Ab.{u + 1}).homEquiv _ _).apply_symm_apply _

/-- On the bounded coefficient sheaves, the comparison with `ℚ̄_ℓ` intertwines the pushforward
map of bounded functions with the precomposition `ℚ̄_ℓ,X ⟶ f_* ℚ̄_ℓ,Y`: both precompose with the
projections `U ×_X Y ⟶ U`. -/
private lemma boundedPushforward_comp_map_padicAlgClSheafToAdicConstantSheaf (f : Y ⟶ X) :
    CondensedQbarScalarConstruction.boundedPushforward l f ≫
        (f)_*[Ab.{u + 1}].map (padicAlgClSheafToAdicConstantSheaf Y l) =
      (padicAlgClSheafToAdicConstantSheaf X l ≫
        (weilCoefficientsForgetAb l X).map (adicConstantSheafToLowerStar l f) :
        _ ⟶ (f)_*[Ab.{u + 1}].obj
          ((weilCoefficientsForgetAb l Y).obj (adicConstantSheaf l Y))) := by
  apply ((sheafificationAdjunction (Scheme.ProEt.topology X) Ab.{u + 1}).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app, Functor.map_comp]
  erw [reassoc_of% CondensedQbarScalarConstruction.boundedPushforward_unit,
    reassoc_of% toSheafify_comp_padicAlgClSheafToAdicConstantSheaf]
  ext U s
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_comp_padicAlgClSheafToAdicConstantSheaf l Y)
    (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj U.unop)))
    ((CondensedQbarScalarConstruction.boundedPrecompose l f).app U s)

variable (l) in
/-- The isomorphism of ring objects `Λ_X ≅ forgetAb ℚ̄_ℓ,X` intertwines the canonical coefficient
morphism `η_f : Λ_X ⟶ f_* Λ_Y` with the precomposition `ℚ̄_ℓ,X ⟶ f_* ℚ̄_ℓ,Y` with the
projections. -/
lemma condensedPushforwardHom_comp_map_condensedRingObjIsoForgetAb_hom (f : Y ⟶ X) :
    condensedPushforwardHom (Profinite.padicAlgClRingObj l) f ≫
        (f)_*[Ab.{u + 1}].map (condensedRingObjIsoForgetAb l Y).hom =
      ((condensedRingObjIsoForgetAb l X).hom ≫
        (weilCoefficientsForgetAb l X).map (adicConstantSheafToLowerStar l f) :
        _ ⟶ (f)_*[Ab.{u + 1}].obj
          ((weilCoefficientsForgetAb l Y).obj (adicConstantSheaf l Y))) := by
  have h (Z : Scheme.{u}) : (condensedRingObjIsoForgetAb l Z).hom =
      (CondensedQbarCoefficientRealization.globalCoefficientIso l Z).hom.hom ≫
        padicAlgClSheafToAdicConstantSheaf Z l := rfl
  rw [h, h, Functor.map_comp, reassoc_of% boundedCoefficient_scheme_naturality l f,
    boundedPushforward_comp_map_padicAlgClSheafToAdicConstantSheaf, Category.assoc]

/-! ### Pushforward -/

variable (l) in
/-- The pushforward commutes strictly with forgetting the `ℚ̄_ℓ`-module structure of sheaves. -/
noncomputable abbrev lowerStarForgetAbIso (f : Y ⟶ X) :
    (f)_*[WeilCoefficients.{u} l] ⋙ weilCoefficientsForgetAb l X ≅
      weilCoefficientsForgetAb l Y ⋙ (f)_*[Ab.{u + 1}] :=
  Functor.sheafPushforwardContinuousCompSheafComposeIso _ _ _ _

/-- The identification `f_* ⋙ forgetAb ≅ forgetAb ⋙ f_*` is monoidal. -/
instance isMonoidal_lowerStarForgetAbIso_hom (f : Y ⟶ X) :
    NatTrans.IsMonoidal (lowerStarForgetAbIso l f).hom :=
  Functor.isMonoidal_sheafPushforwardContinuousCompSheafComposeIso_hom _ _ _ _

-- Rewriting with the monoidality of `f_* ⋙ forgetAb ≅ forgetAb ⋙ f_*` unfolds the sheafified
-- tensor products when unifying the two lax monoidal structures.
variable (l) in
/-- **Pushforward compatibility of the two models of `ℓ`-adic sheaves**: the comparison
`AdicSheaf ℓ ≌ Mod_{Λ}` intertwines the pushforward of sheaves of `ℚ̄_ℓ,Y`-modules with the
pushforward of module objects over `Λ_Y`. The underlying morphisms of abelian sheaves are
identities; the two actions of `Λ_X` agree by
`AlgebraicGeometry.ProEtale.condensedPushforwardHom_comp_map_condensedRingObjIsoForgetAb_hom`. -/
noncomputable def adicLowerStarCompCondensedModIso (f : Y ⟶ X) :
    (f)_*ᵃ[l] ⋙ (adicSheafEquivCondensedMod l X).functor ≅
      (adicSheafEquivCondensedMod l Y).functor ⋙
        CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f :=
  NatIso.ofComponents (fun M ↦ Mod.isoMk (Iso.refl _) (by
    rw [Iso.refl_hom, Category.comp_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]
    have hL : Mod.act (((f)_*ᵃ[l] ⋙ (adicSheafEquivCondensedMod l X).functor).obj M).X =
        (condensedRingObjIsoForgetAb l X).hom ▷ _ ≫
          Functor.LaxMonoidal.μ (weilCoefficientsForgetAb l X) (adicConstantSheaf l X)
            ((f)_*[WeilCoefficients.{u} l].obj M.X) ≫
          (weilCoefficientsForgetAb l X).map (adicConstantSheafToLowerStar l f ▷ _ ≫
            Functor.LaxMonoidal.μ (f)_*[WeilCoefficients.{u} l] (adicConstantSheaf l Y) M.X ≫
            (f)_*[WeilCoefficients.{u} l].map (Mod.act M.X)) := rfl
    have hR : Mod.act (((adicSheafEquivCondensedMod l Y).functor ⋙
        CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).obj M).X =
        condensedPushforwardHom (Profinite.padicAlgClRingObj l) f ▷ _ ≫
          Functor.LaxMonoidal.μ (f)_*[Ab.{u + 1}]
            (condensedRingObj (Profinite.padicAlgClRingObj l) Y)
            ((weilCoefficientsForgetAb l Y).obj M.X) ≫
          (f)_*[Ab.{u + 1}].map ((condensedRingObjIsoForgetAb l Y).hom ▷ _ ≫
            Functor.LaxMonoidal.μ (weilCoefficientsForgetAb l Y) (adicConstantSheaf l Y) M.X ≫
            (weilCoefficientsForgetAb l Y).map (Mod.act M.X)) := rfl
    have hτ := NatTrans.IsMonoidal.tensor (τ := (lowerStarForgetAbIso l f).hom)
      (adicConstantSheaf l Y) M.X
    rw [Functor.LaxMonoidal.comp_μ, Functor.LaxMonoidal.comp_μ] at hτ
    simp only [lowerStarForgetAbIso, Functor.sheafPushforwardContinuousCompSheafComposeIso,
      Iso.refl_hom, NatTrans.id_app] at hτ
    erw [Category.comp_id, id_tensorHom_id, Category.id_comp] at hτ
    refine hL.trans (Eq.trans ?_ hR.symm)
    simp only [Functor.map_comp]
    rw [← Functor.LaxMonoidal.μ_natural_left_assoc (weilCoefficientsForgetAb l X),
      ← Functor.LaxMonoidal.μ_natural_left_assoc (f)_*[Ab.{u + 1}], ← comp_whiskerRight_assoc,
      ← comp_whiskerRight_assoc, condensedPushforwardHom_comp_map_condensedRingObjIsoForgetAb_hom,
      reassoc_of% hτ]
    rfl)) (fun _ ↦ by ext : 1; rfl)

/-- The components of `AlgebraicGeometry.ProEtale.adicLowerStarCompCondensedModIso` are the
identities of the underlying abelian sheaves. -/
lemma adicLowerStarCompCondensedModIso_hom_app_hom (f : Y ⟶ X) (M : AdicSheaf l Y) :
    ((adicLowerStarCompCondensedModIso l f).hom.app M).hom = 𝟙 _ :=
  rfl

/-! ### Pullback -/

variable (l) in
/-- The compatibility of the pushforwards with the comparison of the two models, for the
quasi-inverses of the comparison: `E_Y⁻¹ ⋙ f_* ≅ f_* ⋙ E_X⁻¹`. -/
noncomputable def condensedModInverseCompAdicLowerStarIso (f : Y ⟶ X) :
    (adicSheafEquivCondensedMod l Y).inverse ⋙ (f)_*ᵃ[l] ≅
      CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f ⋙
        (adicSheafEquivCondensedMod l X).inverse :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (adicSheafEquivCondensedMod l X).unitIso ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight (adicLowerStarCompCondensedModIso l f) _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (adicSheafEquivCondensedMod l Y).counitIso _ ≪≫
    Functor.leftUnitor _

variable (l) in
/-- **Pullback compatibility of the two models of `ℓ`-adic sheaves**: the comparison
`AdicSheaf ℓ ≌ Mod_{Λ}` intertwines the pullback of sheaves of `ℚ̄_ℓ,X`-modules with the
pullback of module objects over `Λ_X`. Both composites are left adjoint to the two isomorphic
composites `E_Y⁻¹ ⋙ f_* ≅ f_* ⋙ E_X⁻¹`
(`AlgebraicGeometry.ProEtale.condensedModInverseCompAdicLowerStarIso`), and this is the conjugate
isomorphism. -/
noncomputable def adicUpperStarCompCondensedModIso (f : Y ⟶ X) :
    (f)^*ᵃ[l] ⋙ (adicSheafEquivCondensedMod l Y).functor ≅
      (adicSheafEquivCondensedMod l X).functor ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f :=
  ((conjugateIsoEquiv ((adicUpperStarLowerStarAdjunction l f).comp
      (adicSheafEquivCondensedMod l Y).toAdjunction)
    ((adicSheafEquivCondensedMod l X).toAdjunction.comp
      (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f))).symm
    (condensedModInverseCompAdicLowerStarIso l f)).symm

/-! ### Global sections of pullbacks -/

variable (l X) in
/-- Global sections on `X_proét` commute with forgetting the `ℚ̄_ℓ`-module structure: both are
the sections over the terminal object `X`. -/
noncomputable def globalSectionsForgetAbIso :
    Sheaf.Γ (Scheme.ProEt.topology X) (WeilCoefficients.{u} l) ⋙
        forget₂ (WeilCoefficients.{u} l) Ab.{u + 1} ≅
      weilCoefficientsForgetAb l X ⋙ Sheaf.Γ (Scheme.ProEt.topology X) Ab.{u + 1} :=
  Functor.isoWhiskerRight
      (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId X)) _ ≪≫
    Iso.refl (weilCoefficientsForgetAb l X ⋙
      (sheafSections (Scheme.ProEt.topology X) Ab.{u + 1}).obj (op (Scheme.ProEt.mk (𝟙 X)))) ≪≫
    Functor.isoWhiskerLeft _
      (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId X)).symm

variable (l) in
/-- The global sections on `Y` of the old pullback `s^* F` of an `ℓ`-adic sheaf, as an abelian
group, are naturally the global sections of the underlying abelian sheaf of the new pullback
`s^* (E_X F)` of the corresponding module object over `Λ_X`. -/
noncomputable def globalSectionsAdicUpperStarIso (s : Y ⟶ X) :
    (s)^*ᵃ[l] ⋙ AdicSheaf.forget Y ⋙ Sheaf.Γ _ (WeilCoefficients.{u} l) ⋙
        forget₂ (WeilCoefficients.{u} l) Ab.{u + 1} ≅
      (adicSheafEquivCondensedMod l X).functor ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj l) s ⋙ Mod.forget _ ⋙
          Sheaf.Γ (Scheme.ProEt.topology Y) Ab.{u + 1} :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (globalSectionsForgetAbIso l Y)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Iso.refl (((s)^*ᵃ[l] ⋙ (adicSheafEquivCondensedMod l Y).functor) ⋙
      (Mod.forget _ ⋙ Sheaf.Γ (Scheme.ProEt.topology Y) Ab.{u + 1})) ≪≫
    Functor.isoWhiskerRight (adicUpperStarCompCondensedModIso l s) _ ≪≫
    Functor.associator _ _ _

variable (l) in
/-- The component of `AlgebraicGeometry.ProEtale.globalSectionsAdicUpperStarIso` at an `ℓ`-adic
sheaf `M`: the global sections `Γ(Y, s^* M)` of the pullback of the underlying sheaf of
`ℚ̄_ℓ`-modules, as an abelian group, agree with the global sections of the new pullback. For a
geometric point `s : Spec Ω ⟶ X`, the left hand side is the stalk
`AlgebraicGeometry.WeilSheaf.stalkObj`. -/
noncomputable def globalSectionsAdicUpperStarObjIso (s : Y ⟶ X) (M : AdicSheaf l X) :
    (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1}).obj
        ((Sheaf.Γ _ _).obj ((s)^*[WeilCoefficients.{u} l].obj M.X)) ≅
      (Sheaf.Γ (Scheme.ProEt.topology Y) Ab.{u + 1}).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) s).obj
          ((adicSheafEquivCondensedMod l X).functor.obj M)).X :=
  (globalSectionsAdicUpperStarIso l s).app M

end AlgebraicGeometry.ProEtale
