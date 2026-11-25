/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates

/-! # Finite coefficient projection laws

The finite part of the compact-support projection formula.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open CategoryTheory.SuppliedExchangeProjection
open scoped CategoryTheory.Functor

namespace WeilConjectures

namespace CompactSupportFiniteProjection

-- Keep generic realization comparison data closed while matching their parameters.
attribute [local irreducible] projectionTensorLeftRealization projectionTensorTargetRealization

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

@[irreducible] private def coordinateTransformation (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    ((ProEtale.openImmersionLowerShriek A c.i).mapDerivedCategory ⋙
      (ProEtale.lowerStar A c.g).rightDerivedFunctor) ⋙ ProEtale.derivedTensor A Y ⟶
    (Functor.postcompose₂.obj
      ((ProEtale.openImmersionLowerShriek A c.i).mapDerivedCategory ⋙
        (ProEtale.lowerStar A c.g).rightDerivedFunctor)).obj
      ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj
        (ProEtale.upperStar A f).leftDerivedFunctor).obj (ProEtale.derivedTensor A X)) :=
  projectionMapOfCompactification A c

private theorem coordinateTransformation_app (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    ((coordinateTransformation A c).app K).app L =
      projectionTensorCoordinateComponent A c K L := by
  unfold coordinateTransformation
  exact (projectionTensorCoordinateComponent_eq A c K L).symm

private theorem component_hom (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    (component S f c K L).hom =
      (sourceComparison S f c K L).hom ≫
        (realization (C := C) (E := E) (n := n) (hn := hn) Y).functor.map
          (fixedComponent (C := C) (E := E) (n := n) (hn := hn) f c
            ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj K.obj)
            ((realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj)) ≫
          (targetComparison S f c K L).inv := by
  unfold component projectionFullConjugate
  rfl

private def supportIso (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left) :
    S.finite.support f c ⋙
        (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι ≅
      (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι ⋙
        (realization (C := C) (E := E) (n := n) (hn := hn) X).inverse ⋙
          sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c ⋙
            (realization (C := C) (E := E) (n := n) (hn := hn) Y).functor := by
  let A := Padic.coefficientExtensionRing C.l E n
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let iX := (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
  let I := sixFunctorFiniteSupport D C E n hn f c
  exact S.finiteSupport f c ≪≫ Functor.isoWhiskerLeft iX
    (Functor.isoWhiskerRight RX.counitIso.symm I ≪≫
      Functor.isoWhiskerLeft RX.inverse (sfIntrinsicCompactSupportComparison A c))

private def fixedSupportIso (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left) :=
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  Functor.isoWhiskerRight (supportIso S f c) RY.inverse ≪≫
    Functor.isoWhiskerLeft
      ((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι ⋙
        (realization (C := C) (E := E) (n := n) (hn := hn) X).inverse ⋙
          sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c)
      RY.unitIso.symm

private def pullIso (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) :=
  let A := Padic.coefficientExtensionRing C.l E n
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  S.finitePullback f ≪≫ Functor.isoWhiskerLeft
    (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι
    ((Functor.mapDerivedCategoryCompIso (sfIntrinsicModuleEquivalence Y.obj.left A).inverse
      (AlgebraicGeometry.ProEtale.upperStar
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) f.hom.left ⋙
          (sfIntrinsicModuleEquivalence X.obj.left A).functor)).symm ≪≫
      Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _).symm)

private def fixedPullIso (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) :=
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let iY := (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι
  Functor.isoWhiskerRight (pullIso S f) RX.inverse ≪≫
    Functor.isoWhiskerLeft
      (iY ⋙ RY.inverse ⋙
        sfFixedDerivedPullback (Padic.coefficientExtensionRing C.l E n) f.hom.left)
      RX.unitIso.symm ≪≫
    Functor.isoWhiskerLeft (iY ⋙ RY.inverse)
      (fixedPullComparison (C := C) (E := E) (n := n) f).symm

private def partialTensorIso (S : SixFunctorFiniteOperations D C E n hn)
    (X : SixFunctorSpace D) :
    Functor.uncurry.obj (partialTensor S X) ⋙
        (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι ≅
      ((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι.prod
        (finiteTorConstructible C.l E n hn X.obj.left).ι) ⋙
          Functor.uncurry.obj (tensor (C := C) (E := E) (n := n) (hn := hn) X) := by
  unfold partialTensor
  exact Functor.isoWhiskerRight (Functor.currying.counitIso.app _) _

private def tensorPresentation
    {A B K L M N : Type*} [Category* A] [Category* B] [Category* K]
    [Category* L] [Category* M] [Category* N]
    (J : A ⥤ K) (H : B ⥤ L) (T : K ⥤ L ⥤ M) (V : M ⥤ N) :
    Functor.uncurry.obj ((Functor.postcompose₂.obj V).obj
      ((((Functor.whiskeringLeft₂ _).obj J).obj H).obj T)) ≅
        J.prod H ⋙ Functor.uncurry.obj T ⋙ V :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    simp [Functor.uncurry, Functor.map_comp])

@[irreducible] private def sourceIso (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left) :=
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let iY := (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι
  let iL := (finiteTorConstructible C.l E n hn Y.obj.left).ι
  let TY := fixedTensor (C := C) (E := E) (n := n) Y
  Functor.isoWhiskerLeft ((S.finite.support f c).prod (𝟭 _)) (partialTensorIso S Y) ≪≫
    Functor.isoWhiskerLeft ((S.finite.support f c ⋙ iY).prod iL)
      (tensorPresentation RY.inverse RY.inverse TY RY.functor) ≪≫
    Functor.isoWhiskerRight
      (NatIso.prod (fixedSupportIso S f c) (Iso.refl (iL ⋙ RY.inverse)))
      (Functor.uncurry.obj TY ⋙ RY.functor)

@[irreducible] private def targetIso (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left) :=
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let iX := (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
  let iLX := (finiteTorConstructible C.l E n hn X.obj.left).ι
  let iLY := (finiteTorConstructible C.l E n hn Y.obj.left).ι
  let iT := ObjectProperty.ιOfLE
    (show finiteTorConstructible C.l E n hn Y.obj.left ≤
      intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left from fun _ h ↦ h.1)
  let J := iX ⋙ RX.inverse
  let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c
  let U := fixedDerivedPull (C := C) (E := E) (n := n) f
  let TX := fixedTensor (C := C) (E := E) (n := n) X
  let Q := (𝟭 (sixFunctorFiniteCategory D C E n hn X)).prod (torPull S f)
  Functor.isoWhiskerLeft (Q ⋙ Functor.uncurry.obj (partialTensor S X))
      (supportIso S f c) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft Q (partialTensorIso S X))
      (RX.inverse ⋙ F ⋙ RY.functor) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (iX.prod (torPull S f ⋙ iLX))
        (tensorPresentation RX.inverse RX.inverse TX RX.functor))
      (RX.inverse ⋙ F ⋙ RY.functor) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        (J.prod (torPull S f ⋙ iLX ⋙ RX.inverse) ⋙ Functor.uncurry.obj TX)
        RX.unitIso.symm) (F ⋙ RY.functor) ≪≫
    Functor.isoWhiskerRight
      (NatIso.prod (Iso.refl J) (Functor.isoWhiskerLeft iT (fixedPullIso S f)))
      (Functor.uncurry.obj TX ⋙ F ⋙ RY.functor) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (J.prod (iLY ⋙ RY.inverse))
        (tensorPresentation (𝟭 _) U TX F).symm) RY.functor

private theorem tensorSource_components
    {A B : Type*} [Category* A] [Category* B]
    (T : A ⥤ A ⥤ A) (V : A ⥤ B) {K K' : A} (e : K ≅ K') (L : A) :
    𝟙 _ ≫ 𝟙 _ ≫ V.map ((T.map e.hom).app L ≫ (T.obj K').map (𝟙 L)) =
      (projectionTensorLeftRealization T V e L).hom := by
  simp -implicitDefEqProofs only [(T.obj K').map_id, Category.id_comp, Category.comp_id,
    projectionTensorLeftRealization, Functor.mapIso_hom, Iso.app_hom]

private theorem tensorTarget_components
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (R : A ≌ B) (V : C ⥤ D) (F : A ⥤ C) (T : A ⥤ A ⥤ A)
    (K : A) {L : B} {L' : A} (e : R.inverse.obj L ≅ L')
    {Z : D} (s : Z ≅ V.obj (F.obj
      (R.inverse.obj (R.functor.obj ((T.obj K).obj (R.inverse.obj L)))))) :
    s.hom ≫
      (R.inverse ⋙ F ⋙ V).map (𝟙 (R.functor.obj ((T.obj K).obj (R.inverse.obj L)))) ≫
      (R.inverse ⋙ F ⋙ V).map (𝟙 (R.functor.obj ((T.obj K).obj (R.inverse.obj L)))) ≫
      (F ⋙ V).map (R.unitIso.inv.app ((T.obj K).obj (R.inverse.obj L))) ≫
      (Functor.uncurry.obj T ⋙ F ⋙ V).map (Prod.mkHom (𝟙 K) e.hom) ≫
      V.map (𝟙 (F.obj ((T.obj K).obj L'))) =
        (s ≪≫ projectionTensorTargetRealization R V F T K e).hom := by
  simp -implicitDefEqProofs only [Functor.comp_map, R.inverse.map_id, T.map_id, F.map_id, V.map_id,
    Functor.uncurry_obj_map, NatTrans.id_app,
    Category.id_comp, Functor.map_comp,
    projectionTensorTargetRealization, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_inv, Iso.symm_hom]
  erw [V.map_id]
  erw [Category.id_comp, Category.comp_id]

private theorem sourceIso_hom_raw (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    (sourceIso S f c).hom.app (K, L) =
      let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
      let TY := fixedTensor (C := C) (E := E) (n := n) Y
      𝟙 _ ≫ 𝟙 _ ≫ RY.functor.map
        (((TY.map (fixedSupportRealization S f c K).hom).app (RY.inverse.obj L.obj)) ≫
          (TY.obj _).map (𝟙 _)) := by
  unfold sourceIso
  rfl

private theorem targetIso_hom_raw (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    (targetIso S f c).hom.app (K, L) =
      let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
      let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
      let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c
      let TX := fixedTensor (C := C) (E := E) (n := n) X
      (supportRealization S f c
        (((partialTensor S X).obj K).obj ((torPull S f).obj L))).hom ≫
        (RX.inverse ⋙ F ⋙ RY.functor).map (𝟙 _) ≫
        (RX.inverse ⋙ F ⋙ RY.functor).map (𝟙 _) ≫
        (F ⋙ RY.functor).map (RX.unitIso.inv.app _) ≫
        (Functor.uncurry.obj TX ⋙ F ⋙ RY.functor).map
          (Prod.mkHom (𝟙 (RX.inverse.obj K.obj))
            (fixedPullRealization S f ⟨L.obj, L.property.1⟩).hom) ≫
        RY.functor.map (𝟙 _) := by
  unfold targetIso
  rfl

section
-- Compare the tensor objects before opening the coefficient equivalence or derived functors.
attribute [local irreducible] realization fixedTensor

private theorem sourceIso_app (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    (sourceIso S f c).app (K, L) = sourceComparison S f c K L := by
  apply Iso.ext
  change (sourceIso S f c).hom.app (K, L) = (sourceComparison S f c K L).hom
  rw [sourceIso_hom_raw]
  exact tensorSource_components
    (fixedTensor (C := C) (E := E) (n := n) Y)
    (realization (C := C) (E := E) (n := n) (hn := hn) Y).functor
    (fixedSupportRealization S f c K)
    ((realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj)

private theorem targetIso_app (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    (targetIso S f c).app (K, L) = targetComparison S f c K L := by
  apply Iso.ext
  change (targetIso S f c).hom.app (K, L) = (targetComparison S f c K L).hom
  rw [targetIso_hom_raw]
  exact tensorTarget_components
    (realization (C := C) (E := E) (n := n) (hn := hn) X)
    (realization (C := C) (E := E) (n := n) (hn := hn) Y).functor
    (sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c)
    (fixedTensor (C := C) (E := E) (n := n) X)
    ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj K.obj)
    (L := ((S.finite.pull f).obj ⟨L.obj, L.property.1⟩).obj)
    (L' := (fixedDerivedPull (C := C) (E := E) (n := n) f).obj
      ((realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj))
    (fixedPullRealization S f ⟨L.obj, L.property.1⟩)
    (Z := ((S.finite.support f c).obj
      (((partialTensor S X).obj K).obj ((torPull S f).obj L))).obj)
    (supportRealization S f c
      (((partialTensor S X).obj K).obj ((torPull S f).obj L)))

end

private theorem conjugates_eq
    {A B : Type*} [Category* A] [Category* B]
    {F F' G G' : A ⥤ B} (e : F ≅ F') (d : G ≅ G') (p : A)
    {e' : F.obj p ≅ F'.obj p} {d' : G.obj p ≅ G'.obj p}
    (he : e.app p = e') (hd : d.app p = d') (a : F'.obj p ⟶ G'.obj p) :
    e.hom.app p ≫ a ≫ d.inv.app p = e'.hom ≫ a ≫ d'.inv := by
  cases he
  cases hd
  rfl

private theorem conjugateWhisker_app
    {A B X Y Z W : Type*} [Category* A] [Category* B] [Category* X]
    [Category* Y] [Category* Z] [Category* W]
    (F : A ⥤ X) (G : B ⥤ Y) (V : Z ⥤ W)
    {P Q : X ⥤ Y ⥤ Z} (t : P ⟶ Q) {U T : A × B ⥤ W}
    (e : U ≅ (F.prod G ⋙ Functor.uncurry.obj P) ⋙ V)
    (d : T ≅ (F.prod G ⋙ Functor.uncurry.obj Q) ⋙ V) (K : A) (L : B) :
    (e.hom ≫ Functor.whiskerRight
      (Functor.whiskerLeft (F.prod G) (Functor.uncurry.map t)) V ≫ d.inv).app (K, L) =
      e.hom.app (K, L) ≫ V.map ((t.app (F.obj K)).app (G.obj L)) ≫
        d.inv.app (K, L) := by
  rfl

private theorem coordinateWhisker_app
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {I J B : Type*} [Category* I] [Category* J] [Category* B]
    (F : I ⥤ DerivedCategory (Sheaf (ProEt.topology X) A))
    (G : J ⥤ DerivedCategory (Sheaf (ProEt.topology Y) A))
    (V : DerivedCategory (Sheaf (ProEt.topology Y) A) ⥤ B)
    {U T : I × J ⥤ B}
    (e : U ≅ (F.prod G ⋙ Functor.uncurry.obj
      (((ProEtale.openImmersionLowerShriek A c.i).mapDerivedCategory ⋙
        (ProEtale.lowerStar A c.g).rightDerivedFunctor) ⋙
          ProEtale.derivedTensor A Y)) ⋙ V)
    (d : T ≅ (F.prod G ⋙ Functor.uncurry.obj
      ((Functor.postcompose₂.obj
        ((ProEtale.openImmersionLowerShriek A c.i).mapDerivedCategory ⋙
          (ProEtale.lowerStar A c.g).rightDerivedFunctor)).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj
          (ProEtale.upperStar A f).leftDerivedFunctor).obj
            (ProEtale.derivedTensor A X)))) ⋙ V)
    (K : I) (L : J) :
    (e.hom ≫ Functor.whiskerRight
      (Functor.whiskerLeft (F.prod G)
        (Functor.uncurry.map (coordinateTransformation A c))) V ≫ d.inv).app (K, L) =
      e.hom.app (K, L) ≫
        V.map (projectionTensorCoordinateComponent A c (F.obj K) (G.obj L)) ≫
          d.inv.app (K, L) := by
  exact (conjugateWhisker_app F G V (coordinateTransformation A c) e d K L).trans
    (congrArg (fun t ↦ e.hom.app (K, L) ≫ V.map t ≫ d.inv.app (K, L))
      (coordinateTransformation_app A c (F.obj K) (G.obj L)))

private theorem coordinateWhisker_naturality
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {I J B : Type*} [Category* I] [Category* J] [Category* B]
    (F : I ⥤ DerivedCategory (Sheaf (ProEt.topology X) A))
    (G : J ⥤ DerivedCategory (Sheaf (ProEt.topology Y) A))
    (V : DerivedCategory (Sheaf (ProEt.topology Y) A) ⥤ B)
    {U T : I × J ⥤ B}
    (e : U ≅ (F.prod G ⋙ Functor.uncurry.obj
      (((ProEtale.openImmersionLowerShriek A c.i).mapDerivedCategory ⋙
        (ProEtale.lowerStar A c.g).rightDerivedFunctor) ⋙
          ProEtale.derivedTensor A Y)) ⋙ V)
    (d : T ≅ (F.prod G ⋙ Functor.uncurry.obj
      ((Functor.postcompose₂.obj
        ((ProEtale.openImmersionLowerShriek A c.i).mapDerivedCategory ⋙
          (ProEtale.lowerStar A c.g).rightDerivedFunctor)).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj
          (ProEtale.upperStar A f).leftDerivedFunctor).obj
            (ProEtale.derivedTensor A X)))) ⋙ V)
    (K K' : I) (L L' : J) (a : K ⟶ K') (b : L ⟶ L') :
    U.map (Prod.mkHom a b) ≫
        (e.hom.app (K', L') ≫
          V.map (projectionTensorCoordinateComponent A c (F.obj K') (G.obj L')) ≫
            d.inv.app (K', L')) =
      (e.hom.app (K, L) ≫
        V.map (projectionTensorCoordinateComponent A c (F.obj K) (G.obj L)) ≫
          d.inv.app (K, L)) ≫ T.map (Prod.mkHom a b) := by
  let t := e.hom ≫ Functor.whiskerRight
    (Functor.whiskerLeft (F.prod G)
      (Functor.uncurry.map (coordinateTransformation A c))) V ≫ d.inv
  calc
    _ = U.map (Prod.mkHom a b) ≫ t.app (K', L') :=
      congrArg (fun h ↦ U.map (Prod.mkHom a b) ≫ h)
        (coordinateWhisker_app A c F G V e d K' L').symm
    _ = t.app (K, L) ≫ T.map (Prod.mkHom a b) := t.naturality _
    _ = _ := congrArg (fun h ↦ h ≫ T.map (Prod.mkHom a b))
      (coordinateWhisker_app A c F G V e d K L)

private theorem replace_naturality
    {A : Type*} [Category* A] {X X' Y Y' : A}
    {u : X ⟶ X'} {v : Y ⟶ Y'} {a a' : X' ⟶ Y'} {b b' : X ⟶ Y}
    (h : u ≫ a = b ≫ v) (ha : a = a') (hb : b = b') : u ≫ a' = b' ≫ v := by
  rw [← ha, ← hb]
  exact h

private theorem coordinateComponent_hom
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    let A := Padic.coefficientExtensionRing C.l E n
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    (sourceIso S f c).hom.app (K, L) ≫
      (realization (C := C) (E := E) (n := n) (hn := hn) Y).functor.map
        (projectionTensorCoordinateComponent (ModuleCat.{u + 1} (ULift.{u + 1} A)) c
          ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj K.obj)
          ((realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj)) ≫
        (targetIso S f c).inv.app (K, L) = (component S f c K L).hom := by
  exact (conjugates_eq (sourceIso S f c) (targetIso S f c) (K, L)
    (sourceIso_app S f c K L) (targetIso_app S f c K L) _).trans
      (component_hom S f c K L).symm

/-- The specified finite projection is natural on the two full input domains.
Source: naturality of projectionMapOfCompactification and its coefficient conjugations
(blueprint: lem-sf-finite-projection-input-naturality).
Proof: form the source and target natural coefficient comparisons; conjugate the
published projection natural transformation by them. Evaluate its naturality and
reflect the resulting equation through the faithful constructible inclusion. -/
theorem component_input_naturality (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    {K K' : sixFunctorFiniteCategory D C E n hn X}
    {L L' : finiteTorConstructibleCategory C.l E n hn Y.obj.left}
    (a : K ⟶ K') (b : L ⟶ L') :
    ((partialTensor S Y).map ((S.finite.support f c).map a)).app L ≫
        ((partialTensor S Y).obj ((S.finite.support f c).obj K')).map b ≫
        component S f c K' L' =
      component S f c K L ≫ (S.finite.support f c).map
        (((partialTensor S X).map a).app ((torPull S f).obj L) ≫
          ((partialTensor S X).obj K').map ((torPull S f).map b)) := by
  apply (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι.map_injective
  let A := Padic.coefficientExtensionRing C.l E n
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let J := (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι ⋙ RX.inverse
  let H := (finiteTorConstructible C.l E n hn Y.obj.left).ι ⋙ RY.inverse
  have h := replace_naturality
    (coordinateWhisker_naturality (ModuleCat.{u + 1} (ULift.{u + 1} A)) c J H RY.functor
      (sourceIso S f c) (targetIso S f c) K K' L L' a b)
    (coordinateComponent_hom S f c K' L') (coordinateComponent_hom S f c K L)
  simpa -implicitDefEqProofs only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.id_map, Functor.id_obj, Functor.uncurry_obj_map, Functor.map_comp,
    ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom,
    Category.assoc] using h

end CompactSupportFiniteProjection
end WeilConjectures
