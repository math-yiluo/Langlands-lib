/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comp

/-!
# Coherent integer families pulled back from a base scheme

Let `P` be a coherent integer family in `D(S_ét)`
(`CategoryTheory.MonoidalCategory.IntTensorFamily`):
objects `P m`, `m ∈ ℤ`, with identifications `P 0 ≅ Λ_S` and `P a ⊗ᴸ P b ≅ P (a + b)` satisfying
the unit and associativity laws. Since the derived pullback `Lπ^*` along `π : X ⟶ S` is monoidal,
the pullbacks `Lπ^* P m` form a coherent family on `X`
(`AlgebraicGeometry.Etale.pullbackIntTensorFamily`). For `f : X ⟶ Y` over `S`, the composition
isomorphisms of the derived pullbacks identify `Lf^* Lπ_Y^* P m` with `Lπ_X^* P m`
(`AlgebraicGeometry.Etale.pullbackIntTensorFamilyIso`), and these identifications are compatible
with the composition of morphisms and with the products of the families.

This is how the Tate twists are built: from one family on the universal base scheme on which the
exponent of the coefficient ring is invertible, all the compatibilities between the twists on
different schemes are formal consequences of the coherence of the derived pullback.

The statements are written with `AlgebraicGeometry.Etale.derivedTensor` and the unitors and
associator of `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`, so that they specialize
to `A = ModuleCat Λ` without the kernel having to compare two presentations of the derived
tensor product.

## Main definitions

- `AlgebraicGeometry.Etale.pullbackIntTensorFamily`: the family `Lπ^* P` on `X`.
- `AlgebraicGeometry.Etale.pullbackIntTensorFamilyIso`: `Lf^* Lπ_Y^* P m ≅ Lπ_X^* P m`.

## Main statements

- `AlgebraicGeometry.Etale.pullbackIntTensorFamilyIso_comp`: compatibility with composition.
- `AlgebraicGeometry.Etale.map_addIso_pullbackIntTensorFamilyIso`: compatibility with the
  products.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Generic

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X : Scheme.{u}} (Q : IntTensorFamily (DerivedCategory (Sheaf X.smallEtaleTopology A)))

/-- The identification `Q a ⊗ᴸ Q b ≅ Q (a + b)` of a coherent family in `D(X_ét)`, written with
the derived tensor product. Over `A = ModuleCat Λ` this presentation avoids the comparison of the
tensor product of the monoidal structure on `D(X_ét)` with the derived tensor product, which the
kernel does not perform in reasonable time. -/
noncomputable def _root_.CategoryTheory.MonoidalCategory.IntTensorFamily.derivedTensorAddIso
    (a b : ℤ) : ((derivedTensor A X).obj (Q.obj a)).obj (Q.obj b) ≅ Q.obj (a + b) :=
  Q.addIso a b

/-- The left unit law of a coherent family in `D(X_ét)`, written with the derived tensor
product. -/
lemma _root_.CategoryTheory.MonoidalCategory.IntTensorFamily.derivedTensor_zero_left (m : ℤ) :
    ((derivedTensor A X).map Q.zeroIso.hom).app (Q.obj m) ≫
        (derivedTensorLeftUnitor A X (Q.obj m)).hom =
      (Q.derivedTensorAddIso 0 m).hom ≫ eqToHom (by rw [zero_add]) :=
  Q.zero_left m

/-- The right unit law of a coherent family in `D(X_ét)`, written with the derived tensor
product. -/
lemma _root_.CategoryTheory.MonoidalCategory.IntTensorFamily.derivedTensor_zero_right (m : ℤ) :
    ((derivedTensor A X).obj (Q.obj m)).map Q.zeroIso.hom ≫
        (derivedTensorRightUnitor A X (Q.obj m)).hom =
      (Q.derivedTensorAddIso m 0).hom ≫ eqToHom (by rw [add_zero]) :=
  Q.zero_right m

/-- The associativity law of a coherent family in `D(X_ét)`, written with the derived tensor
product. -/
lemma _root_.CategoryTheory.MonoidalCategory.IntTensorFamily.derivedTensor_assoc (a b c : ℤ) :
    ((derivedTensor A X).map (Q.derivedTensorAddIso a b).hom).app (Q.obj c) ≫
        (Q.derivedTensorAddIso (a + b) c).hom =
      (derivedTensorAssociator A X (Q.obj a) (Q.obj b) (Q.obj c)).hom ≫
        ((derivedTensor A X).obj (Q.obj a)).map (Q.derivedTensorAddIso b c).hom ≫
          (Q.derivedTensorAddIso a (b + c)).hom ≫ eqToHom (by rw [add_assoc]) :=
  Q.assoc a b c

/-- Every member of a coherent family in `D(X_ét)` is invertible for the derived tensor product,
with inverse the member of opposite index. -/
lemma _root_.CategoryTheory.MonoidalCategory.IntTensorFamily.exists_derivedTensor_iso (m : ℤ) :
    ∃ M, Nonempty (((derivedTensor A X).obj (Q.obj m)).obj M ≅ 𝟙_ _) ∧
      Nonempty (((derivedTensor A X).obj M).obj (Q.obj m) ≅ 𝟙_ _) :=
  ⟨Q.obj (-m), ⟨Q.derivedTensorAddIso m (-m) ≪≫ eqToIso (by rw [add_neg_cancel]) ≪≫ Q.zeroIso⟩,
    ⟨Q.derivedTensorAddIso (-m) m ≪≫ eqToIso (by rw [neg_add_cancel]) ≪≫ Q.zeroIso⟩⟩

end Generic

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

variable {S : Scheme.{u}} (P : IntTensorFamily (DerivedCategory (Sheaf S.smallEtaleTopology A)))

/-- The pullback `Lπ^* P` along `π : X ⟶ S` of a coherent family `P` in `D(S_ét)`: the derived
pullback is monoidal, with invertible structure maps. -/
noncomputable def pullbackIntTensorFamily {X : Scheme.{u}} (π : X ⟶ S) :
    IntTensorFamily (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  letI := leftDerivedUpperStarOplaxMonoidal A π
  haveI := isIso_leftDerivedUpperStarOplaxMonoidal_η A π
  haveI := isIso_leftDerivedUpperStarOplaxMonoidal_δ A π
  P.map L((π)^*[A])

@[simp]
lemma pullbackIntTensorFamily_obj {X : Scheme.{u}} (π : X ⟶ S) (m : ℤ) :
    (pullbackIntTensorFamily A P π).obj m = L((π)^*[A]).obj (P.obj m) :=
  rfl

/-- For `f : X ⟶ Y` over `S`, the identification `Lf^* Lπ_Y^* P m ≅ Lπ_X^* P m` given by the
composition isomorphism of the derived pullbacks. -/
noncomputable def pullbackIntTensorFamilyIso {X Y : Scheme.{u}} (f : X ⟶ Y) (πX : X ⟶ S)
    (πY : Y ⟶ S) (h : πX = f ≫ πY) (m : ℤ) :
    L((f)^*[A]).obj ((pullbackIntTensorFamily A P πY).obj m) ≅
      (pullbackIntTensorFamily A P πX).obj m :=
  ((leftDerivedUpperStarComp A f πY πX h).app (P.obj m)).symm

/-- The identifications `Lf^* Lπ_Y^* P m ≅ Lπ_X^* P m` are compatible with the composition of
morphisms: for `f : X ⟶ Y` and `g : Y ⟶ Z`, the identification for `f ≫ g` is the composite
`L(f ≫ g)^* Lπ_Z^* P m ≅ Lf^* Lg^* Lπ_Z^* P m ≅ Lf^* Lπ_Y^* P m ≅ Lπ_X^* P m`. -/
lemma pullbackIntTensorFamilyIso_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (πX : X ⟶ S) (πY : Y ⟶ S) (πZ : Z ⟶ S) (hX : πX = (f ≫ g) ≫ πZ) (hY : πY = g ≫ πZ)
    (hX' : πX = f ≫ πY) (m : ℤ) :
    pullbackIntTensorFamilyIso A P (f ≫ g) πX πZ hX m =
      (leftDerivedUpperStarComp A f g).app _ ≪≫
        L((f)^*[A]).mapIso (pullbackIntTensorFamilyIso A P g πY πZ hY m) ≪≫
          pullbackIntTensorFamilyIso A P f πX πY hX' m := by
  have key := (leftDerivedUpperStarComp_assoc'_app A f g πZ (f ≫ g) πY πX rfl hY hX
    (P.obj m)).symm
  ext
  simp only [pullbackIntTensorFamilyIso, Iso.symm_hom, Iso.app_inv, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, pullbackIntTensorFamily_obj]
  rw [← cancel_epi ((leftDerivedUpperStarComp A (f ≫ g) πZ πX hX).hom.app (P.obj m)),
    Iso.hom_inv_id_app, reassoc_of% key, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]

/-- The identifications `Lf^* Lπ_Y^* P m ≅ Lπ_X^* P m` are compatible with the products of the
families, along the tensor comparison `Lf^*(K ⊗ᴸ M) ≅ Lf^* K ⊗ᴸ Lf^* M`. -/
lemma map_addIso_pullbackIntTensorFamilyIso {X Y : Scheme.{u}} (f : X ⟶ Y) (πX : X ⟶ S)
    (πY : Y ⟶ S) (h : πX = f ≫ πY) (m m' : ℤ) :
    L((f)^*[A]).map ((pullbackIntTensorFamily A P πY).addIso m m').hom ≫
        (pullbackIntTensorFamilyIso A P f πX πY h (m + m')).hom =
      (leftDerivedUpperStarTensorIso A f _ _).hom ≫
        ((derivedTensor A X).map (pullbackIntTensorFamilyIso A P f πX πY h m).hom).app _ ≫
          ((derivedTensor A X).obj ((pullbackIntTensorFamily A P πX).obj m)).map
            (pullbackIntTensorFamilyIso A P f πX πY h m').hom ≫
            ((pullbackIntTensorFamily A P πX).addIso m m').hom := by
  let := leftDerivedUpperStarOplaxMonoidal A πX
  let := leftDerivedUpperStarOplaxMonoidal A πY
  let := leftDerivedUpperStarOplaxMonoidal A f
  have := isIso_leftDerivedUpperStarOplaxMonoidal_η A πX
  have := isIso_leftDerivedUpperStarOplaxMonoidal_δ A πX
  have := isIso_leftDerivedUpperStarOplaxMonoidal_η A πY
  have := isIso_leftDerivedUpperStarOplaxMonoidal_δ A πY
  have := isIso_leftDerivedUpperStarOplaxMonoidal_η A f
  have := isIso_leftDerivedUpperStarOplaxMonoidal_δ A f
  let c := leftDerivedUpperStarComp A f πY πX h
  have hc : ∀ K M, δ L((πX)^*[A]) K M ≫ (c.hom.app K ⊗ₘ c.hom.app M) =
      c.hom.app (K ⊗ M) ≫ L((f)^*[A]).map (δ L((πY)^*[A]) K M) ≫ δ L((f)^*[A]) _ _ :=
    leftDerivedUpperStarTensorComparison_comp A f πY πX h
  have key := IntTensorFamily.map_addIso_comp P L((πY)^*[A]) L((f)^*[A]) L((πX)^*[A]) c hc m m'
  simp only [pullbackIntTensorFamilyIso, Iso.symm_hom, Iso.app_inv]
  refine key.trans ?_
  rw [tensorHom_def]
  simp only [Category.assoc]
  rfl

section Copy

/-! ### Transport to families equal to the pulled back ones -/

variable {X Y : Scheme.{u}} (FX : ℤ → DerivedCategory (Sheaf X.smallEtaleTopology A))
  (FY : ℤ → DerivedCategory (Sheaf Y.smallEtaleTopology A))

/-- The identification `Lf^* F_Y m ≅ F_X m` for families `F_X`, `F_Y` equal to the pulled back
families `Lπ_X^* P` and `Lπ_Y^* P`. -/
noncomputable def pullbackIntTensorFamilyCopyIso (f : X ⟶ Y) (πX : X ⟶ S) (πY : Y ⟶ S)
    (h : πX = f ≫ πY) (hX : FX = (pullbackIntTensorFamily A P πX).obj)
    (hY : FY = (pullbackIntTensorFamily A P πY).obj) (m : ℤ) :
    L((f)^*[A]).obj (FY m) ≅ FX m :=
  L((f)^*[A]).mapIso (eqToIso (congrFun hY m)) ≪≫ pullbackIntTensorFamilyIso A P f πX πY h m ≪≫
    eqToIso (congrFun hX m).symm

/-- `AlgebraicGeometry.Etale.pullbackIntTensorFamilyIso_comp` for families equal to the pulled
back families. -/
lemma pullbackIntTensorFamilyCopyIso_comp {Z : Scheme.{u}}
    (FZ : ℤ → DerivedCategory (Sheaf Z.smallEtaleTopology A)) (f : X ⟶ Y) (g : Y ⟶ Z)
    (πX : X ⟶ S) (πY : Y ⟶ S) (πZ : Z ⟶ S) (hX : πX = (f ≫ g) ≫ πZ) (hY : πY = g ≫ πZ)
    (hX' : πX = f ≫ πY) (hFX : FX = (pullbackIntTensorFamily A P πX).obj)
    (hFY : FY = (pullbackIntTensorFamily A P πY).obj)
    (hFZ : FZ = (pullbackIntTensorFamily A P πZ).obj) (m : ℤ) :
    pullbackIntTensorFamilyCopyIso A P FX FZ (f ≫ g) πX πZ hX hFX hFZ m =
      (leftDerivedUpperStarComp A f g).app _ ≪≫
        L((f)^*[A]).mapIso (pullbackIntTensorFamilyCopyIso A P FY FZ g πY πZ hY hFY hFZ m) ≪≫
          pullbackIntTensorFamilyCopyIso A P FX FY f πX πY hX' hFX hFY m := by
  subst hFX hFY hFZ
  simp only [pullbackIntTensorFamilyCopyIso, eqToIso_refl, Functor.mapIso_refl, Iso.refl_trans,
    Iso.trans_refl]
  exact pullbackIntTensorFamilyIso_comp A P f g πX πY πZ hX hY hX' m

/-- `AlgebraicGeometry.Etale.map_addIso_pullbackIntTensorFamilyIso` for families equal to the
pulled back families. -/
lemma map_addIso_pullbackIntTensorFamilyCopyIso (f : X ⟶ Y) (πX : X ⟶ S) (πY : Y ⟶ S)
    (h : πX = f ≫ πY) (hX : FX = (pullbackIntTensorFamily A P πX).obj)
    (hY : FY = (pullbackIntTensorFamily A P πY).obj) (m m' : ℤ) :
    L((f)^*[A]).map
        (((pullbackIntTensorFamily A P πY).copy FY hY).derivedTensorAddIso m m').hom ≫
        (pullbackIntTensorFamilyCopyIso A P FX FY f πX πY h hX hY (m + m')).hom =
      (leftDerivedUpperStarTensorIso A f _ _).hom ≫
        ((derivedTensor A X).map
          (pullbackIntTensorFamilyCopyIso A P FX FY f πX πY h hX hY m).hom).app _ ≫
          ((derivedTensor A X).obj (FX m)).map
            (pullbackIntTensorFamilyCopyIso A P FX FY f πX πY h hX hY m').hom ≫
            (((pullbackIntTensorFamily A P πX).copy FX hX).derivedTensorAddIso m m').hom := by
  subst hX hY
  simp only [pullbackIntTensorFamilyCopyIso, IntTensorFamily.derivedTensorAddIso,
    IntTensorFamily.copy_addIso, eqToIso_refl,
    Functor.mapIso_refl, Iso.refl_trans, Iso.trans_refl]
  exact map_addIso_pullbackIntTensorFamilyIso A P f πX πY h m m'

end Copy

end Etale

end AlgebraicGeometry
