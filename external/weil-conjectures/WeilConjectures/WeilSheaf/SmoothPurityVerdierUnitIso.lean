/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangePoint
public import WeilConjectures.PoincareDuality.Biduality.Constructible
public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExceptionalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.SmoothProjection

/-!
# The relative A1' for the proper part: `πZ^* Rp^! ℚ̄_ℓ ≅ Rp̄^! ℚ̄_ℓ` by Verdier duality

Let `k` be a finite field with algebraic closure `k̄`, and `f : X ⟶ Y` a morphism of separated
`k`-schemes of finite type, with geometric fibre `f̄ : X̄ ⟶ Ȳ`. We build **an** isomorphism of
bounded constructible `ℚ̄_ℓ`-complexes `πX^* Rf^! ℚ̄_ℓ ≅ Rf̄^! ℚ̄_ℓ`
(`geometricFiberUpperShriekUnitIso`), by Verdier duality, following Houyi's reduction of the
relative case to the point case:

1. `Rf^! ℚ̄_ℓ ≅ Rf^! RHom(ω_Y, ω_Y) ≅ RHom(f^* ω_Y, Rf^! ω_Y) ≅ RHom(f^* ω_Y, ω_X)`, by biduality
   at the unit (`isIso_verdierBiduality`), the exceptional internal hom exchange
   `RHom(f^* M, Rf^! N) ≅ Rf^! RHom(M, N)` (`CategoryTheory.Verdier.exceptionalHomMap`) and
   `Rf^! ω_Y ≅ ω_X` (`upperShriekDualizingComplexIso`);
2. `πX^* RHom(A, ω_X) ≅ RHom(πX^* A, ω_X̄)`: weakly étale pullback commutes with internal homs
   (`isIso_nearbyDualityMap_upperStarOfMap_id_of_weaklyEtale`) and `πX^* ω_X ≅ ω_X̄` is the point
   case `isIso_smoothUnitBaseChange_geometricFiberLowerShriekBaseChangePoint` (A1' over a point,
   for the structure morphism of `X`);
3. `πX^* f^* ω_Y ≅ f̄^* πY^* ω_Y ≅ f̄^* ω_Ȳ`, by the point case for `Y`;
4. step 1 backwards on `X̄ ⟶ Ȳ`.

No smoothness or properness of `f` is used. For `p` **proper**, the **endomorphism trick**
`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_iso` turns the existence of
such an isomorphism into the invertibility of the canonical base change map
`πZ^* Rp^! ℚ̄_ℓ ⟶ Rp̄^! πP^* ℚ̄_ℓ` of `Rp^!` at the unit
(`isIso_upperShriekBaseChangeOfMap_app_unit_of_iso`, for any proper `p` in a cartesian square
over a weakly étale `πP`, and `isIso_upperShriekBaseChangeOfMap_app_unit_geometricFiber` for the
geometric fibre). The relative Nagata pasting is in
`WeilConjectures.WeilSheaf.SmoothPurityVerdierUnitBaseChangeRelative`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

/-! ### The absolute part: `Rf^! ℚ̄_ℓ ≅ RHom(f^* ω_Y, ω_X)`, over any field -/

section Absolute

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

variable (Y) in
/-- **Biduality at the unit**: `ℚ̄_ℓ ≅ RHom(ω_Y, ω_Y)`, from the biduality isomorphism
`ℚ̄_ℓ ≅ 𝔻_Y 𝔻_Y ℚ̄_ℓ` (`isIso_verdierBiduality`) and `RHom(ℚ̄_ℓ, ω_Y) ≅ ω_Y`
(`MonoidalClosed.unitNatIso`). -/
def unitIsoIhomDualizingComplex :
    𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) ≅
      (ihom (dualizingComplex ℓ Y)).obj (dualizingComplex ℓ Y) :=
  haveI := isIso_verdierBiduality ℓ (X := Y) (𝟙_ _)
  asIso (verdierBiduality ℓ (X := Y) (𝟙_ _)) ≪≫
    ihomIsoOfIsoLeft (unitNatIso.app (dualizingComplex ℓ Y)).symm (dualizingComplex ℓ Y)

variable (f : X ⟶ Y)

/-- **The exceptional internal hom exchange** `RHom(f^* M, Rf^! N) ≅ Rf^! RHom(M, N)` on bounded
constructible `ℚ̄_ℓ`-complexes (blueprint `lemma-external-duality-trace-morphism--2`), from the
derived projection formula `boundedConstructibleExceptionalProjection` and the exceptional
adjunction, as `TraceFormula.TraceClass.exceptionalHomIso`. -/
def upperShriekExceptionalHomIso (M N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (ihom ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj M)).obj
        ((boundedConstructibleUpperShriek ℓ f).obj N) ≅
      (boundedConstructibleUpperShriek ℓ f).obj ((ihom M).obj N) :=
  haveI := Verdier.isIso_exceptionalHomMap_of_isIso
    (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleExceptionalProjection ℓ f) M N
  asIso (Verdier.exceptionalHomMap (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleExceptionalProjection ℓ f) M N)

/-- **`Rf^! ℚ̄_ℓ ≅ RHom(f^* ω_Y, ω_X)`** for an arbitrary morphism `f : X ⟶ Y` of separated
`k`-schemes of finite type:
`Rf^! ℚ̄_ℓ ≅ Rf^! RHom(ω_Y, ω_Y) ≅ RHom(f^* ω_Y, Rf^! ω_Y) ≅ RHom(f^* ω_Y, ω_X)`. -/
def upperShriekUnitIsoIhomUpperStarDualizingComplex :
    (boundedConstructibleUpperShriek ℓ f).obj (𝟙_ _) ≅
      (ihom ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
        (dualizingComplex ℓ Y))).obj (dualizingComplex ℓ X) :=
  (boundedConstructibleUpperShriek ℓ f).mapIso (unitIsoIhomDualizingComplex ℓ Y) ≪≫
    (upperShriekExceptionalHomIso ℓ f (dualizingComplex ℓ Y) (dualizingComplex ℓ Y)).symm ≪≫
    (ihom _).mapIso (upperShriekDualizingComplexIso ℓ f)

end Absolute

/-! ### Pullbacks commute with pullbacks across fields (no open-immersion hypothesis) -/

section Square

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ ℓ)]
  {X Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (f : X ⟶ Y) (f' : X' ⟶ Y') {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left}

/-- The pullbacks commute with the pullbacks across fields: `f^* ⋙ πX^* ≅ πY^* ⋙ f'^*` on bounded
constructible complexes for a commutative square `πX ≫ f = f' ≫ πY`, from the composition
isomorphisms of the derived pullbacks (`boundedConstructibleUpperStarCompUpperStarOfMapIso`
without its open-immersion hypotheses). -/
def boundedConstructibleUpperStarSquareIso (h : πX ≫ f.left = f'.left ≫ πY) :
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f ⋙
        boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') πX ≅
      boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') πY ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f' :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ObjectProperty.liftCompιIso _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleUpperStarCompatibility _ ℓ f) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarComp _ πX f.left).symm ≪≫
      eqToIso (by rw [h]) ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarComp _ f'.left πY) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ObjectProperty.liftCompιIso _ _ _).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleUpperStarCompatibility _ ℓ f').symm ≪≫
      (Functor.associator _ _ _).symm)


/-- **Weakly étale pullback commutes with internal homs**, as an isomorphism
`π^* RHom(A, B) ≅ RHom(π^* A, π^* B)` on bounded constructible complexes
(`isIso_nearbyDualityMap_upperStarOfMap_id_of_weaklyEtale`). -/
def upperStarOfMapIhomIso (π : X'.left ⟶ X.left) [WeaklyEtale π]
    (A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') π).obj ((ihom A).obj B) ≅
      (ihom ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') π).obj A)).obj
        ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') π).obj B) :=
  haveI : IsIso ((Functor.LaxMonoidal.ihomComparison
      (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') π) A).app B) := by
    have := isIso_nearbyDualityMap_upperStarOfMap_id_of_weaklyEtale ℓ (P := X) (P' := X') π B A
    rwa [Verdier.nearbyDualityMap_id_eq_ihomComparison] at this
  asIso ((Functor.LaxMonoidal.ihomComparison
    (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') π) A).app B)

/-- **An isomorphism `πX^* Rf^! ℚ̄_ℓ ≅ Rf'^! ℚ̄_ℓ` by Verdier duality**, for a commutative square
`πX ≫ f = f' ≫ πY` with `πX` weakly étale, given isomorphisms `πX^* ω_X ≅ ω_X'` and
`πY^* ω_Y ≅ ω_Y'`:
```
πX^* Rf^! ℚ̄_ℓ ≅ πX^* RHom(f^* ω_Y, ω_X) ≅ RHom(πX^* f^* ω_Y, ω_X') ≅ RHom(f'^* πY^* ω_Y, ω_X')
  ≅ RHom(f'^* ω_Y', ω_X') ≅ Rf'^! ℚ̄_ℓ.
```
It is not claimed to be the exceptional base change map; see
`isIso_upperShriekBaseChangeOfMap_app_unit_of_iso` for the endomorphism trick that deduces the
invertibility of the latter from the existence of this isomorphism, for `f` proper. -/
def upperShriekUnitIsoOfDualizingComplexIso (h : πX ≫ f.left = f'.left ≫ πY) [WeaklyEtale πX]
    (ωX : (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') πX).obj
      (dualizingComplex ℓ X) ≅ dualizingComplex ℓ X')
    (ωY : (boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') πY).obj
      (dualizingComplex ℓ Y) ≅ dualizingComplex ℓ Y') :
    (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') πX).obj
        ((boundedConstructibleUpperShriek ℓ f).obj (𝟙_ _)) ≅
      (boundedConstructibleUpperShriek ℓ f').obj (𝟙_ _) :=
  (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') πX).mapIso
      (upperShriekUnitIsoIhomUpperStarDualizingComplex ℓ f) ≪≫
    upperStarOfMapIhomIso ℓ πX _ _ ≪≫
    (ihom _).mapIso ωX ≪≫
    ihomIsoOfIsoLeft
      ((boundedConstructibleUpperStarSquareIso ℓ f f' h).app (dualizingComplex ℓ Y) ≪≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f').mapIso ωY)
      (dualizingComplex ℓ X') ≪≫
    (upperShriekUnitIsoIhomUpperStarDualizingComplex ℓ f').symm

end Square

/-! ### Pullbacks across the base field `k ⟶ k̄` -/

section GeometricFiber

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable (k) in
/-- The unit of the pullback along `Spec k̄ ⟶ Spec k`, `πs^* ℚ̄_ℓ ⟶ ℚ̄_ℓ`, read as the counit datum
`e` of `smoothUnitBaseChange`. -/
def pointUnitBaseChangeCounit :
    (boundedConstructibleUpperStarOfMap ℓ (X := point k) (Y := geometricFiberOver (point k))
      (point k).hom.geometricFiberProj).obj (𝟙_ _) ⟶ 𝟙_ _ :=
  (Functor.Monoidal.εIso (boundedConstructibleUpperStarOfMap ℓ (X := point k)
    (Y := geometricFiberOver (point k)) (point k).hom.geometricFiberProj)).inv

instance : IsIso (pointUnitBaseChangeCounit ℓ k) :=
  inferInstanceAs (IsIso (Iso.inv _))

variable (X : Over (Spec (.of k)))
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **The dualizing complex commutes with the change of the base field `k ⟶ k̄`**, as an
isomorphism `πX^* ω_X ≅ ω_X̄`: the point case of A1'
(`isIso_smoothUnitBaseChange_geometricFiberLowerShriekBaseChangePoint`, for the structure
morphism `a_X : X ⟶ Spec k`) gives `πX^* Ra_X^! ℚ̄_ℓ ≅ Rā_X^! ℚ̄_ℓ`, and `ā_X` followed by the
isomorphism `Spec k̄ ×_k Spec k ⟶ Spec k̄` is the structure morphism of `X̄`. -/
def geometricFiberDualizingComplexIso :
    (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := geometricFiberOver X)
        X.hom.geometricFiberProj).obj (dualizingComplex ℓ X) ≅
      dualizingComplex ℓ (geometricFiberOver X) :=
  haveI := isIso_smoothUnitBaseChange_geometricFiberLowerShriekBaseChangePoint ℓ (toPoint X)
    (pointUnitBaseChangeCounit ℓ k)
  haveI : IsIso (toPoint (geometricFiberOver (point k))).left := by
    rw [toPoint_left]
    infer_instance
  asIso (smoothUnitBaseChange ℓ (toPoint X) (geometricFiberOverMap (toPoint X))
      (geometricFiberLowerShriekBaseChangePoint ℓ (toPoint X)) (pointUnitBaseChangeCounit ℓ k)) ≪≫
    (boundedConstructibleUpperShriek ℓ (geometricFiberOverMap (toPoint X))).mapIso
      (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ
        (toPoint (geometricFiberOver (point k)))).symm ≪≫
    upperShriekDualizingComplexIso ℓ (geometricFiberOverMap (toPoint X))

variable {X} {Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- **Some isomorphism `πX^* Rf^! ℚ̄_ℓ ≅ Rf̄^! ℚ̄_ℓ`** for an arbitrary morphism `f : X ⟶ Y` of
separated `k`-schemes of finite type, `k` finite, along `k ⟶ k̄`: Verdier duality
(`upperShriekUnitIsoOfDualizingComplexIso`) with the point case for `X` and `Y`
(`geometricFiberDualizingComplexIso`). -/
def geometricFiberUpperShriekUnitIso :
    (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := geometricFiberOver X)
        X.hom.geometricFiberProj).obj ((boundedConstructibleUpperShriek ℓ f).obj (𝟙_ _)) ≅
      (boundedConstructibleUpperShriek ℓ (geometricFiberOverMap f)).obj (𝟙_ _) :=
  upperShriekUnitIsoOfDualizingComplexIso ℓ f (geometricFiberOverMap f)
    (isPullback_geometricFiberOverMap f).w (geometricFiberDualizingComplexIso ℓ X)
    (geometricFiberDualizingComplexIso ℓ Y)

end GeometricFiber

/-! ### The endomorphism trick for a proper morphism -/

section Trick

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ ℓ)]
  {Z P : Over (Spec (.of k₁))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {Z' P' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {p : Z ⟶ P} {p' : Z' ⟶ P'} [IsProper p.left] [IsProper p'.left]
  {πP : P'.left ⟶ P.left} {πZ : Z'.left ⟶ Z.left}

/-- **The endomorphism trick at the unit**: for a cartesian square `πZ ≫ p = p' ≫ πP` with `p`,
`p'` proper and `πP` weakly étale, the base change map `πZ^* Rp^! ℚ̄_ℓ ⟶ Rp'^! πP^* ℚ̄_ℓ` of `Rp^!`
at the unit is invertible as soon as its source and target are isomorphic in **some** way:
`Rp'_*` of it is invertible (`isIso_lowerStar_map_upperShriekBaseChangeOfMap_app`, from the
commutation of `πP^*` with `RHom(Rp_* ℚ̄_ℓ, ℚ̄_ℓ)`), and
`isIso_upperShriekBaseChangeOfMap_app_of_iso` concludes. -/
theorem isIso_upperShriekBaseChangeOfMap_app_unit_of_iso (sq : IsPullback πZ p'.left p.left πP)
    [WeaklyEtale πP]
    (ψ : (boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := Z') πZ).obj
        ((boundedConstructibleUpperShriek ℓ p).obj (𝟙_ _)) ≅
      (boundedConstructibleUpperShriek ℓ p').obj (𝟙_ _)) :
    IsIso ((upperShriekBaseChangeOfMap ℓ sq).app (𝟙_ _)) := by
  have h := isIso_nearbyDualityMap_upperStarOfMap_id_of_weaklyEtale ℓ (P := P) (P' := P') πP
    (𝟙_ _) ((boundedConstructibleLowerStar ℓ p).obj (𝟙_ _))
  have := isIso_lowerStar_map_upperShriekBaseChangeOfMap_app ℓ sq (𝟙_ _) h
  exact isIso_upperShriekBaseChangeOfMap_app_of_iso ℓ sq (𝟙_ _)
    (ψ ≪≫ (boundedConstructibleUpperShriek ℓ p').mapIso
      (Functor.Monoidal.εIso (boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := P') πP)))

end Trick

end AlgebraicGeometry.ProEtale.CondensedRing
