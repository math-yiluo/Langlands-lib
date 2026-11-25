/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelEquivalenceFunctoriality
public import WeilConjectures.AlgebraicGeometry.GeometricFiberFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.AbsoluteFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.WeilSheaf.Category
public import WeilConjectures.WeilSheaf.StrictWeilComplex

/-!
# Weil sheaves in the condensed model

Let `k₀` be a finite field, `X` a scheme over `k₀`, `X̄` its geometric fiber and
`Fr_X = 𝟙 × σ : X̄ ≅ X̄` its geometric Galois Frobenius. The pro-étale Weil sheaves of the old
model, `AlgebraicGeometry.ProEtaleWeilSheaf k₀ l X`, are `ℓ`-adic sheaves `F` (sheaves of
`ℚ̄_ℓ,X̄`-modules in sheaves of `ℚ̄_ℓ`-modules) together with an isomorphism
`(Fr_X⁻¹)_* F ≅ F`. Through the equivalence of the two models of `ℓ`-adic sheaves
`E : AdicSheaf ℓ X̄ ≌ Mod_{Λ_X̄}` (`AlgebraicGeometry.ProEtale.adicSheafEquivCondensedMod`), with
`Λ = ℚ̲̄_ℓ` the condensed ring `Profinite.padicAlgClRingObj l`, and its compatibility with the
pushforward (`AlgebraicGeometry.ProEtale.adicLowerStarCompCondensedModIso`), these become module
objects `M` over `Λ_X̄` in abelian sheaves on `X̄_proét` together with an isomorphism
`(Fr_X⁻¹)_* M ≅ M`; and since `Fr_X` is an automorphism, `(Fr_X⁻¹)_* ≅ Fr_X^*` also in the new
model (`AlgebraicGeometry.ProEtale.CondensedRing.upperStarIsoLowerStarInv`), so these are the
Weil objects `Fr_X^* M ≅ M` for the automorphism `Fr_X` of `X̄` in the new model.

## Main results

- `CategoryTheory.Endofunctor.IsoAlgebra.isEquivalence_mapOfNatIso`: the transport of algebras
  with invertible structure morphism along an equivalence is an equivalence.
- `AlgebraicGeometry.ProEtale.CondensedRing.lowerStarEquivalenceOfIso`: for an isomorphism
  `e : X ≅ Y`, the pushforward `e_*` of module objects over `Λ` is an equivalence.
- `AlgebraicGeometry.ProEtale.CondensedRing.upperStarIsoLowerStarInv`: `(e.hom)^* ≅ (e.inv)_*`
  on module objects over `Λ`.
- `AlgebraicGeometry.ProEtaleWeilSheaf.toCondensed`: the equivalence (`IsEquivalence`, additive)
  from Weil sheaves of the old model to condensed `ℚ̲̄_ℓ`-modules on `X̄` with an isomorphism
  `(Fr_X⁻¹)_* M ≅ M`.
- `AlgebraicGeometry.ProEtaleWeilSheaf.toCondensedUpperStar`: the equivalence (`IsEquivalence`,
  additive) from Weil sheaves of the old model to condensed `ℚ̲̄_ℓ`-modules on `X̄` with an
  isomorphism `Fr_X^* M ≅ M`, i.e. Weil objects for `Fr_X` in the new model.

## Frobenius conventions

Both models above use the geometric Galois Frobenius `Fr_X = 𝟙 × σ` of `X̄` (`σ = Spec` of the
geometric Frobenius `z ↦ z^{1/q}` of `k̄`): the old model through the pushforward along `Fr_X⁻¹`,
the new one through the pullback along `Fr_X`. The trace-formula chapter uses instead, for
objects on a model `X₀` pulled back to `X̄`, the scheme Frobenius `Φ = Φ₀ × 𝟙`
(`AlgebraicGeometry.Scheme.Hom.geometricFiberFrobenius`). In the new model the two pullbacks
agree:

- `AlgebraicGeometry.ProEtale.CondensedRing.upperStarGeometricFiberFrobeniusIso`:
  `Φ^* ≅ Fr_X^*`, since `Φ = F ≫ Fr_X` for the absolute `q`-power Frobenius `F` of `X̄`
  (`AlgebraicGeometry.Scheme.Hom.geometricFiberFrobenius_eq_iterateFrobenius_comp`), which acts
  trivially on the pro-étale topos.
- `AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberWeil`: for the projection
  `p : X̄ ⟶ X₀`, the pullback `p^* M` of a module object on `X₀` carries the canonical Weil
  structure `Fr_X^* p^* M ≅ (Fr_X ≫ p)^* M = p^* M`, as `Fr_X ≫ p = p`; and
  `AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberWeilLowerStar` is the same in the
  pushforward convention `(Fr_X⁻¹)_* p^* M ≅ p^* M` of the target of
  `AlgebraicGeometry.ProEtaleWeilSheaf.toCondensed`.
-/

@[expose] public section

universe w w' v v' u u'

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {F : C ⥤ C} {G : D ⥤ D} {L : C ⥤ D} (e : L ⋙ G ≅ F ⋙ L)

/-- The transport along an essentially surjective fully faithful functor is essentially
surjective: an algebra `Φ : G b ≅ b` is the transport of the algebra on a preimage `a` of `b`
whose structure isomorphism is the preimage of `G` applied to `L a ≅ b`, then `Φ`. -/
instance essSurj_mapOfNatIso [L.Full] [L.Faithful] [L.EssSurj] : (mapOfNatIso e).EssSurj where
  mem_essImage M := by
    let c := L.objObjPreimageIso M.carrier
    let φ : F.obj (L.objPreimage M.carrier) ≅ L.objPreimage M.carrier :=
      L.preimageIso (e.symm.app _ ≪≫ G.mapIso c ≪≫ M.str ≪≫ c.symm)
    refine ⟨mk _ φ, ⟨ObjectProperty.isoMk _ (Algebra.isoMk c ?_)⟩⟩
    simp [mapOfNatIso, Algebra.mapOfNatTrans, φ]

/-- The transport of algebras with invertible structure morphism along an equivalence of
categories is an equivalence of categories. -/
instance isEquivalence_mapOfNatIso [L.IsEquivalence] : (mapOfNatIso e).IsEquivalence where

end CategoryTheory.Endofunctor.IsoAlgebra

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}}

/-- For an isomorphism of schemes `e : X ≅ Y`, the pushforward `e_*` of module objects over `Λ`
is an equivalence, with quasi-inverse `(e⁻¹)_*`. -/
noncomputable def lowerStarEquivalenceOfIso (e : X ≅ Y) :
    CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ≌
      CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y) :=
  CategoryTheory.Equivalence.mk (lowerStar Λ e.hom) (lowerStar Λ e.inv)
    ((lowerStarId Λ X).symm ≪≫ lowerStarCongr Λ e.hom_inv_id.symm ≪≫
      (lowerStarComp Λ e.hom e.inv).symm)
    (lowerStarComp Λ e.inv e.hom ≪≫ lowerStarCongr Λ e.inv_hom_id ≪≫ lowerStarId Λ Y)

/-- For an isomorphism of schemes `e : X ≅ Y`, the pullback along `e` of module objects over `Λ`
is the pushforward along `e⁻¹`: both are left adjoint to `e_*`. This is the new-model analogue
of `AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv`. -/
noncomputable def upperStarIsoLowerStarInv (e : X ≅ Y) :
    upperStar Λ e.hom ≅ lowerStar Λ e.inv :=
  (upperStarLowerStarAdjunction Λ e.hom).leftAdjointUniq
    (lowerStarEquivalenceOfIso Λ e).symm.toAdjunction

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The equivalence of the two models of `ℓ`-adic sheaves is additive. -/
instance (Y : Scheme.{u}) : (adicSheafEquivCondensedMod l Y).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

namespace ProEtaleWeilSheaf

/-- The comparison `E ⋙ (Fr_X⁻¹)_* ≅ (Fr_X⁻¹)_*ᵃ ⋙ E` of the Frobenius pullbacks of the two
models along the equivalence `E` of `AlgebraicGeometry.ProEtale.adicSheafEquivCondensedMod`. -/
noncomputable def condensedFrobeniusComparison :
    (adicSheafEquivCondensedMod l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor ⋙
        CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv ≅
      WeilSheaf.frobeniusPullback k₀ l X ⋙
        (adicSheafEquivCondensedMod l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor :=
  (adicLowerStarCompCondensedModIso l _).symm

/-- **Weil sheaves in the condensed model**: a pro-étale Weil sheaf `(F, (Fr_X⁻¹)_* F ≅ F)` of
the old model becomes the condensed `ℚ̲̄_ℓ`-module `E F` on `X̄` with the Frobenius structure
`(Fr_X⁻¹)_* (E F) ≅ E ((Fr_X⁻¹)_* F) ≅ E F`. -/
noncomputable def toCondensed :
    ProEtaleWeilSheaf k₀ l X ⥤ Endofunctor.IsoAlgebra
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv) :=
  Endofunctor.IsoAlgebra.mapOfNatIso (condensedFrobeniusComparison k₀ l X)

instance : (toCondensed k₀ l X).IsEquivalence :=
  Endofunctor.IsoAlgebra.isEquivalence_mapOfNatIso _

instance : (toCondensed k₀ l X).Additive :=
  Endofunctor.IsoAlgebra.additive_mapOfNatIso _

@[simp]
lemma toCondensed_obj_carrier (F : ProEtaleWeilSheaf k₀ l X) :
    ((toCondensed k₀ l X).obj F).carrier =
      (adicSheafEquivCondensedMod l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.obj
        F.carrier :=
  rfl

/-- The Frobenius structure of `E F` is `(Fr_X⁻¹)_* (E F) ≅ E ((Fr_X⁻¹)_* F) ≅ E F`; the first
isomorphism has identity underlying morphism of abelian sheaves
(`AlgebraicGeometry.ProEtale.adicLowerStarCompCondensedModIso_hom_app_hom`). -/
lemma toCondensed_obj_str (F : ProEtaleWeilSheaf k₀ l X) :
    ((toCondensed k₀ l X).obj F).str =
      (condensedFrobeniusComparison k₀ l X).app F.carrier ≪≫
        (adicSheafEquivCondensedMod l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.mapIso F.str :=
  Endofunctor.IsoAlgebra.mapOfNatIso_obj_str _ F

/-- The comparison `E ⋙ Fr_X^* ≅ (Fr_X⁻¹)_*ᵃ ⋙ E` of the Frobenius pullback of the old model with
the pullback along `Fr_X` of the new model, through
`AlgebraicGeometry.ProEtale.CondensedRing.upperStarIsoLowerStarInv`. -/
noncomputable def condensedUpperStarFrobeniusComparison :
    (adicSheafEquivCondensedMod l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom ≅
      WeilSheaf.frobeniusPullback k₀ l X ⋙
        (adicSheafEquivCondensedMod l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor :=
  Functor.isoWhiskerLeft _ (CondensedRing.upperStarIsoLowerStarInv _ _) ≪≫
    condensedFrobeniusComparison k₀ l X

/-- **Weil sheaves as Weil objects of the condensed model**: a pro-étale Weil sheaf
`(F, (Fr_X⁻¹)_* F ≅ F)` of the old model becomes the condensed `ℚ̲̄_ℓ`-module `E F` on `X̄` with
the Weil structure `Fr_X^* (E F) ≅ (Fr_X⁻¹)_* (E F) ≅ E ((Fr_X⁻¹)_* F) ≅ E F` for the
automorphism `Fr_X` of `X̄`. -/
noncomputable def toCondensedUpperStar :
    ProEtaleWeilSheaf k₀ l X ⥤ Endofunctor.IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom) :=
  Endofunctor.IsoAlgebra.mapOfNatIso (condensedUpperStarFrobeniusComparison k₀ l X)

instance : (toCondensedUpperStar k₀ l X).IsEquivalence :=
  Endofunctor.IsoAlgebra.isEquivalence_mapOfNatIso _

instance : (toCondensedUpperStar k₀ l X).Additive :=
  Endofunctor.IsoAlgebra.additive_mapOfNatIso _

@[simp]
lemma toCondensedUpperStar_obj_carrier (F : ProEtaleWeilSheaf k₀ l X) :
    ((toCondensedUpperStar k₀ l X).obj F).carrier =
      (adicSheafEquivCondensedMod l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.obj
        F.carrier :=
  rfl

lemma toCondensedUpperStar_obj_str (F : ProEtaleWeilSheaf k₀ l X) :
    ((toCondensedUpperStar k₀ l X).obj F).str =
      (condensedUpperStarFrobeniusComparison k₀ l X).app F.carrier ≪≫
        (adicSheafEquivCondensedMod l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.mapIso F.str :=
  Endofunctor.IsoAlgebra.mapOfNatIso_obj_str _ F

end ProEtaleWeilSheaf

end AlgebraicGeometry

/-! ### Frobenius conventions and pulled-back objects -/

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- The scheme Frobenius `Φ = Φ₀ × 𝟙` of the geometric fibre is the absolute `q`-power
Frobenius followed by the geometric Galois Frobenius: `Φ = F ≫ Fr_X`. -/
lemma geometricFiberFrobenius_eq_iterateFrobenius_comp :
    f.geometricFiberFrobenius =
      f.geometricFiber.iterateFrobenius (FiniteField.ringChar_prime k)
          f.isOfCharacteristic_geometricFiber (FiniteField.frobeniusExponent k) ≫
        f.geometricGaloisFrobenius.asIso.hom := by
  rw [iterateFrobenius_geometricFiber_eq, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- **Frobenius conventions**: on module objects over `Λ` on the geometric fibre `X̄`, the
pullback along the scheme Frobenius `Φ = Φ₀ × 𝟙` (the base change of the `q`-power Frobenius
`Φ₀` of `X₀`, `AlgebraicGeometry.Scheme.Hom.geometricFiberFrobenius`) is isomorphic to the
pullback along the geometric Galois Frobenius `Fr_X = 𝟙 × σ`: since `Φ = F ≫ Fr_X` for the
absolute `q`-power Frobenius `F` of `X̄`
(`AlgebraicGeometry.Scheme.Hom.iterateFrobenius_geometricFiber_eq`), and `F^* ≅ 𝟭`
(`AlgebraicGeometry.ProEtale.CondensedRing.upperStarIterateFrobeniusIso`). -/
noncomputable def upperStarGeometricFiberFrobeniusIso :
    upperStar Λ f.geometricFiberFrobenius ≅ upperStar Λ f.geometricGaloisFrobenius.asIso.hom :=
  upperStarCongr Λ (Scheme.Hom.geometricFiberFrobenius_eq_iterateFrobenius_comp f) ≪≫
    upperStarComp Λ _ _ ≪≫
    Functor.isoWhiskerLeft _ (upperStarIterateFrobeniusIso Λ (FiniteField.ringChar_prime k)
      f.isOfCharacteristic_geometricFiber _) ≪≫
    Functor.rightUnitor _

/-- The pullback `p^*` along the projection `p : X̄ ⟶ X₀` of the geometric fibre is invariant
under the geometric Galois Frobenius: `p^* ⋙ Fr_X^* ≅ (Fr_X ≫ p)^* = p^*`, since
`Fr_X ≫ p = p`
(`AlgebraicGeometry.Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj`). -/
noncomputable def geometricFiberProjUpperStarFrobeniusIso :
    upperStar Λ f.geometricFiberProj ⋙ upperStar Λ f.geometricGaloisFrobenius.asIso.hom ≅
      upperStar Λ f.geometricFiberProj :=
  (upperStarComp Λ _ _).symm ≪≫
    upperStarCongr Λ (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj f)

/-- The Weil structure of a pulled-back object: a module object `M` over `Λ` on the model `X₀`
gives the Weil object `p^* M` on the geometric fibre for the automorphism `Fr_X`, with structure
isomorphism `Fr_X^* p^* M ≅ (Fr_X ≫ p)^* M = p^* M`
(`AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberProjUpperStarFrobeniusIso`). -/
@[simps obj map]
noncomputable def geometricFiberWeil :
    CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X₀) Ab.{u + 1}) (condensedRingObj Λ X₀) ⥤
      Endofunctor.IsoAlgebra (upperStar Λ f.geometricGaloisFrobenius.asIso.hom) where
  obj M := Endofunctor.IsoAlgebra.mk _ ((geometricFiberProjUpperStarFrobeniusIso Λ f).app M)
  map φ := ObjectProperty.homMk
    { f := (upperStar Λ f.geometricFiberProj).map φ
      h := (geometricFiberProjUpperStarFrobeniusIso Λ f).hom.naturality φ }

/-- The geometric fibre Weil objects composed with the forgetful functor are the pullback along
the projection `p : X̄ ⟶ X₀`. -/
lemma geometricFiberWeil_comp_forget :
    geometricFiberWeil Λ f ⋙ Endofunctor.IsoAlgebra.forget _ = upperStar Λ f.geometricFiberProj :=
  rfl

/-- The pullback `p^*` along the projection `p : X̄ ⟶ X₀` is invariant under the inverse of the
geometric Galois Frobenius in the pushforward convention of the old model:
`p^* ⋙ (Fr_X⁻¹)_* ≅ p^* ⋙ Fr_X^* ≅ p^*`. -/
noncomputable def geometricFiberProjLowerStarFrobeniusIso :
    upperStar Λ f.geometricFiberProj ⋙ lowerStar Λ f.geometricGaloisFrobenius.asIso.inv ≅
      upperStar Λ f.geometricFiberProj :=
  Functor.isoWhiskerLeft _ (upperStarIsoLowerStarInv Λ _).symm ≪≫
    geometricFiberProjUpperStarFrobeniusIso Λ f

/-- The Weil structure of a pulled-back object in the pushforward convention: a module object
`M` over `Λ` on `X₀` gives `p^* M` on the geometric fibre with the structure isomorphism
`(Fr_X⁻¹)_* p^* M ≅ p^* M`
(`AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberProjLowerStarFrobeniusIso`), an object
of the target of `AlgebraicGeometry.ProEtaleWeilSheaf.toCondensed`. -/
@[simps obj map]
noncomputable def geometricFiberWeilLowerStar :
    CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X₀) Ab.{u + 1}) (condensedRingObj Λ X₀) ⥤
      Endofunctor.IsoAlgebra (lowerStar Λ f.geometricGaloisFrobenius.asIso.inv) where
  obj M := Endofunctor.IsoAlgebra.mk _ ((geometricFiberProjLowerStarFrobeniusIso Λ f).app M)
  map φ := ObjectProperty.homMk
    { f := (upperStar Λ f.geometricFiberProj).map φ
      h := (geometricFiberProjLowerStarFrobeniusIso Λ f).hom.naturality φ }

end AlgebraicGeometry.ProEtale.CondensedRing
