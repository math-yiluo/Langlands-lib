/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.TensorSingle
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.TensorBaseChange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# The homology sheaves of the base change map for a pushforward tensored with a sheaf

Fix a commutative square `h ≫ f' = e ≫ g`, `p : X' ⟶ X` and a sheaf `𝓕` on `T`, and put
`N = Lf'^* Rg_* 𝓕[0]`. For a sheaf `𝓖` on `X` and `q : ℤ`, the base change map
(`AlgebraicGeometry.Etale.tensorBaseChangeMap`) at `(Lp^* 𝓖[0], 𝓕[0])` induces on `Hᵠ` a map

`Hᵠ(Lp^* 𝓖[0] ⊗ᴸ τ^{≤q} N) ⟶ Hᵠ(Lp^* 𝓖[0] ⊗ᴸ N) ⟶ Hᵠ(Rh_*(Lh^* Lp^* 𝓖[0] ⊗ᴸ Le^* 𝓕[0]))
  ⟶ Hᵠ(Rh_*((h^* p^* 𝓖 ⊗ e^* 𝓕)[0]))`

natural in `𝓖` (`AlgebraicGeometry.Etale.tensorBaseChangeHomologyMap`). Its source and target are
functors of `𝓖` which, for `𝓖` killed by the Jacobson radical, are computed by underived tensor
products, and for `𝓖` flat it is the map induced on `Hᵠ` by the base change map.

The constructions are carried out for a general coefficient category `A`; instantiating them
afterwards (for `A = ModuleCat Λ`) is much cheaper than elaborating them for a specific `A`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {X X' S' T Y : Scheme.{u}} (p : X' ⟶ X) (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S')
  (w : h ≫ f' = e ≫ g) (𝓕 : Sheaf T.smallEtaleTopology A)

/-- The complex `N = Lf'^* Rg_* 𝓕[0]` on `X'`. -/
noncomputable abbrev tensorBaseChangeComplex : DerivedCategory (Sheaf X'.smallEtaleTopology A) :=
  L((f')^*[A]).obj (R((g)_*[A]).obj ((DerivedCategory.singleFunctor _ 0).obj 𝓕))

/-- The source `𝓖 ↦ Hᵠ(Lp^* 𝓖[0] ⊗ᴸ τ^{≤q} N)` of the degree-`q` base change map. -/
noncomputable def tensorBaseChangeHomologySource (q : ℤ) :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf X'.smallEtaleTopology A :=
  DerivedCategory.singleFunctor _ 0 ⋙ L((p)^*[A]) ⋙
    (-⊗ᴸ-(X')[A]).flip.obj
      ((DerivedCategory.TStructure.t.truncLE q).obj (tensorBaseChangeComplex A f' g 𝓕)) ⋙
    DerivedCategory.homologyFunctor _ q

/-- The functor `𝓖 ↦ h^* p^* 𝓖 ⊗ e^* 𝓕`. -/
noncomputable abbrev tensorBaseChangeHomologyTargetSheaf :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf Y.smallEtaleTopology A :=
  (p)^*[A] ⋙ (h)^*[A] ⋙ tensorRight ((e)^*[A].obj 𝓕)

/-- The functor `𝓖 ↦ Hᵠ(Rh_* 𝓖[0])`, the higher direct image along `h`. -/
noncomputable abbrev higherDirectImageFunctor (q : ℤ) :
    Sheaf Y.smallEtaleTopology A ⥤ Sheaf X'.smallEtaleTopology A :=
  DerivedCategory.singleFunctor _ 0 ⋙ R((h)_*[A]) ⋙ DerivedCategory.homologyFunctor _ q

/-- The target `𝓖 ↦ Hᵠ(Rh_*((h^* p^* 𝓖 ⊗ e^* 𝓕)[0]))` of the degree-`q` base change map. -/
noncomputable def tensorBaseChangeHomologyTarget (q : ℤ) :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf X'.smallEtaleTopology A :=
  tensorBaseChangeHomologyTargetSheaf A p h e 𝓕 ⋙ higherDirectImageFunctor A h q

/-- The truncation part `Hᵠ(Lp^* 𝓖[0] ⊗ᴸ τ^{≤q} N) ⟶ Hᵠ(Lp^* 𝓖[0] ⊗ᴸ N)` of the degree-`q` base
change map. -/
noncomputable def tensorBaseChangeHomologyTrunc (q : ℤ) :
    tensorBaseChangeHomologySource A p f' g 𝓕 q ⟶
      DerivedCategory.singleFunctor _ 0 ⋙ L((p)^*[A]) ⋙
        (-⊗ᴸ-(X')[A]).flip.obj (tensorBaseChangeComplex A f' g 𝓕) ⋙
          DerivedCategory.homologyFunctor _ q :=
  Functor.whiskerLeft (DerivedCategory.singleFunctor _ 0)
    (Functor.whiskerLeft L((p)^*[A])
      (Functor.whiskerRight ((-⊗ᴸ-(X')[A]).flip.map
        ((DerivedCategory.TStructure.t.truncLEι q).app (tensorBaseChangeComplex A f' g 𝓕)))
        (DerivedCategory.homologyFunctor _ q)))

variable [Etale.UpperStarPreservesFlat A]

/-- The base change part `Hᵠ(Lp^* 𝓖[0] ⊗ᴸ N) ⟶ Hᵠ(Rh_*(Lh^* Lp^* 𝓖[0] ⊗ᴸ Le^* 𝓕[0]))` of the
degree-`q` base change map. -/
noncomputable def tensorBaseChangeHomologyBaseChange (q : ℤ) :
    DerivedCategory.singleFunctor _ 0 ⋙ L((p)^*[A]) ⋙
        (-⊗ᴸ-(X')[A]).flip.obj (tensorBaseChangeComplex A f' g 𝓕) ⋙
          DerivedCategory.homologyFunctor _ q ⟶
      DerivedCategory.singleFunctor _ 0 ⋙ L((p)^*[A]) ⋙
        (L((h)^*[A]) ⋙ (-⊗ᴸ-(Y)[A]).flip.obj (L((e)^*[A]).obj
            ((DerivedCategory.singleFunctor _ 0).obj 𝓕)) ⋙ R((h)_*[A])) ⋙
          DerivedCategory.homologyFunctor _ q :=
  Functor.whiskerLeft (DerivedCategory.singleFunctor _ 0)
    (Functor.whiskerLeft L((p)^*[A])
      (Functor.whiskerRight (tensorBaseChangeMapLeft A h e f' g w
        ((DerivedCategory.singleFunctor _ 0).obj 𝓕)) (DerivedCategory.homologyFunctor _ q)))

/-- The identification `Hᵠ(Rh_*(Lh^* Lp^* 𝓖[0] ⊗ᴸ Le^* 𝓕[0])) ≅ Hᵠ(Rh_*(h^* p^* 𝓖[0] ⊗ᴸ e^* 𝓕[0]))`
of the derived pullbacks of sheaves with the underived ones. -/
noncomputable def tensorBaseChangeHomologyPullbackIso (q : ℤ) :
    DerivedCategory.singleFunctor _ 0 ⋙ L((p)^*[A]) ⋙
        (L((h)^*[A]) ⋙ (-⊗ᴸ-(Y)[A]).flip.obj (L((e)^*[A]).obj
            ((DerivedCategory.singleFunctor _ 0).obj 𝓕)) ⋙ R((h)_*[A])) ⋙
          DerivedCategory.homologyFunctor _ q ≅
      (p)^*[A] ⋙ (h)^*[A] ⋙
        (DerivedCategory.singleFunctor _ 0 ⋙
          tensorRight ((DerivedCategory.singleFunctor _ 0).obj ((e)^*[A].obj 𝓕))) ⋙
          R((h)_*[A]) ⋙ DerivedCategory.homologyFunctor _ q :=
  let H := DerivedCategory.homologyFunctor (Sheaf X'.smallEtaleTopology A) q
  let sX := DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0
  let sX' := DerivedCategory.singleFunctor (Sheaf X'.smallEtaleTopology A) 0
  let sY := DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology A) 0
  let Φ := (-⊗ᴸ-(Y)[A]).flip.obj (L((e)^*[A]).obj ((DerivedCategory.singleFunctor _ 0).obj 𝓕))
  let Ψ := tensorRight (sY.obj ((e)^*[A].obj 𝓕))
  let b : Φ ≅ Ψ := (-⊗ᴸ-(Y)[A]).flip.mapIso
    ((singleFunctorCompLeftDerivedUpperStarIso A e).app 𝓕)
  let rest := (Φ ⋙ R((h)_*[A])) ⋙ H
  let i₁ : sX ⋙ L((p)^*[A]) ⋙ (L((h)^*[A]) ⋙ Φ ⋙ R((h)_*[A])) ⋙ H ≅
      sX ⋙ L((p)^*[A]) ⋙ L((h)^*[A]) ⋙ rest :=
    Functor.isoWhiskerLeft sX (Functor.isoWhiskerLeft L((p)^*[A])
      (Functor.associator L((h)^*[A]) (Φ ⋙ R((h)_*[A])) H))
  let i₂ : sX ⋙ L((p)^*[A]) ⋙ L((h)^*[A]) ⋙ rest ≅ (p)^*[A] ⋙ sX' ⋙ L((h)^*[A]) ⋙ rest :=
    (Functor.associator sX L((p)^*[A]) (L((h)^*[A]) ⋙ rest)).symm ≪≫
      Functor.isoWhiskerRight (singleFunctorCompLeftDerivedUpperStarIso A p) _ ≪≫
      Functor.associator (p)^*[A] sX' (L((h)^*[A]) ⋙ rest)
  let i₃ : (p)^*[A] ⋙ sX' ⋙ L((h)^*[A]) ⋙ rest ≅ (p)^*[A] ⋙ (h)^*[A] ⋙ sY ⋙ rest :=
    Functor.isoWhiskerLeft (p)^*[A]
      ((Functor.associator sX' L((h)^*[A]) rest).symm ≪≫
        Functor.isoWhiskerRight (singleFunctorCompLeftDerivedUpperStarIso A h) rest ≪≫
        Functor.associator (h)^*[A] sY rest)
  let i₄ : sY ⋙ rest ≅ (sY ⋙ Ψ) ⋙ R((h)_*[A]) ⋙ H :=
    Functor.isoWhiskerLeft sY (Functor.associator Φ R((h)_*[A]) H) ≪≫
      (Functor.associator sY Φ (R((h)_*[A]) ⋙ H)).symm ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft sY b) (R((h)_*[A]) ⋙ H)
  i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ Functor.isoWhiskerLeft (p)^*[A] (Functor.isoWhiskerLeft (h)^*[A] i₄)

/-- The comparison `Hᵠ(Rh_*(h^* p^* 𝓖[0] ⊗ᴸ e^* 𝓕[0])) ⟶ Hᵠ(Rh_*((h^* p^* 𝓖 ⊗ e^* 𝓕)[0]))` of the
derived and the underived tensor products. -/
noncomputable def tensorBaseChangeHomologyComparison (q : ℤ) :
    (p)^*[A] ⋙ (h)^*[A] ⋙
        (DerivedCategory.singleFunctor _ 0 ⋙
          tensorRight ((DerivedCategory.singleFunctor _ 0).obj ((e)^*[A].obj 𝓕))) ⋙
          R((h)_*[A]) ⋙ DerivedCategory.homologyFunctor _ q ⟶
      tensorBaseChangeHomologyTarget A p h e 𝓕 q :=
  Functor.whiskerLeft (p)^*[A]
    (Functor.whiskerLeft (h)^*[A]
      (Functor.whiskerRight (singleFunctorTensorToSingle ((e)^*[A].obj 𝓕))
        (R((h)_*[A]) ⋙ DerivedCategory.homologyFunctor _ q) ≫
      (Functor.associator _ _ _).hom))

/-- The degree-`q` base change map
`Hᵠ(Lp^* 𝓖[0] ⊗ᴸ τ^{≤q} N) ⟶ Hᵠ(Rh_*((h^* p^* 𝓖 ⊗ e^* 𝓕)[0]))`, natural in the sheaf `𝓖` on `X`:
the truncation `τ^{≤q} N ⟶ N`, the base change map
(`AlgebraicGeometry.Etale.tensorBaseChangeMapLeft`) and the comparison of the derived and the
underived tensor products (`AlgebraicGeometry.Etale.singleFunctorTensorToSingle`). -/
noncomputable def tensorBaseChangeHomologyMap (q : ℤ) :
    tensorBaseChangeHomologySource A p f' g 𝓕 q ⟶ tensorBaseChangeHomologyTarget A p h e 𝓕 q :=
  tensorBaseChangeHomologyTrunc A p f' g 𝓕 q ≫
    tensorBaseChangeHomologyBaseChange A p h e f' g w 𝓕 q ≫
      (tensorBaseChangeHomologyPullbackIso A p h e 𝓕 q).hom ≫
        tensorBaseChangeHomologyComparison A p h e 𝓕 q

end Etale

end AlgebraicGeometry
