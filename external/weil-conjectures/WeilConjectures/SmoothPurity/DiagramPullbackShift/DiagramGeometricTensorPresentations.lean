/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.SectionCounit

/-! # Geometric tensor presentations for pulled-back condensed coefficients

The coefficient sheaf is `condensedRingObj Λ X = p_X^* Λ`. Every functor and comparison
below is the native module-object construction. In particular the tensor comparison is
normalized by its derived-functor counit, and the inverse-image compositor is the mate of
the specified direct-image compositor. No alternate coefficient category is introduced.

Source: latest blueprint, `sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence`,
maps-used sentence, and `sec-proetale-coefficients/sk-prop-sf-open-closed-triangle/`
`prose-03-02`; Stacks 03D2, 03D8, 03EL, 0G7E and 07A4.
(blueprint: lem-pur-diagram-geometric-tensor-presentations).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale (condensedRingObj condensedPullbackHom)
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing


variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The geometric presentation and resolving normalization of the fixed native functors.
All maps in these assertions are specified constructions, rather than chosen witnesses.
The normalization is stated on all homotopy complexes, hence also on K-flat representatives.
Source: the maps-used sentence and Stacks 03D2, 03D8, 03EL, 0G7E and 07A4.
(blueprint: def-pur-native-geometric-tensor-presentations). -/
structure GeometricTensorPresentations : Prop where
  /-- Pullback of the coefficient ring is the canonical isomorphism. -/
  coefficient : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsIso (condensedPullbackHom Λ f)
  /-- Module inverse image is exact on the entire abelian category. -/
  limits : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), PreservesFiniteLimits (upperStar Λ f)
  /-- Inverse image also preserves finite colimits. -/
  colimits : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), PreservesFiniteColimits (upperStar Λ f)
  /-- Its right adjoint is the specified geometric direct image. -/
  adjunction : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    Nonempty (upperStar Λ f ⊣ lowerStar Λ f)
  /-- Total derived pullback is canonically the exact termwise pullback: the specified
  comparison `leftDerivedUpperStarIsoMapDerivedCategory` is the one compatible with the
  derived-functor counit. -/
  derived : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    Functor.whiskerLeft DerivedCategory.Qh (leftDerivedUpperStarIsoMapDerivedCategory Λ f).hom ≫
        (upperStar Λ f).mapDerivedCategoryFactorsh.hom =
      (upperStar Λ f).leftDerivedFunctorCounit
  /-- The actual termwise functor preserves K-flat resolving complexes. -/
  resolving : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ),
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
        (((upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj P)
  /-- The specified derived tensor comparison is invertible. -/
  tensor : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsIso (leftDerivedUpperStarTensor Λ f)
  /-- The representative square is exactly the defining derived-functor square. -/
  normalized : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Qh).obj DerivedCategory.Qh).map
        (leftDerivedUpperStarTensor Λ f) ≫ leftDerivedUpperStarTensorRightCounit Λ f =
      leftDerivedUpperStarTensorLeftCounit Λ f
  /-- Direct-image compositors have the specified underlying sheaf maps. -/
  sections : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    ((lowerStarComp Λ f g).hom.app M).hom =
      (AlgebraicGeometry.ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app M.X
  /-- Inverse-image compositors are the adjunction mates of those direct-image maps. -/
  mate : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    conjugateIsoEquiv ((upperStarLowerStarAdjunction Λ g).comp
        (upperStarLowerStarAdjunction Λ f)) (upperStarLowerStarAdjunction Λ (f ≫ g))
      (upperStarComp Λ f g) = lowerStarComp Λ f g
  /-- The two unit routes agree as morphisms, before deriving or reducing coefficients. -/
  unit : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)),
    (upperStarLowerStarAdjunction Λ g).unit.app M ≫
        (lowerStar Λ g).map
          ((upperStarLowerStarAdjunction Λ f).unit.app ((upperStar Λ g).obj M)) ≫
        (lowerStarComp Λ f g).hom.app ((upperStar Λ f).obj ((upperStar Λ g).obj M)) =
      (upperStarLowerStarAdjunction Λ (f ≫ g)).unit.app M ≫
        (lowerStar Λ (f ≫ g)).map ((upperStarComp Λ f g).hom.app M)

/-- Native geometric inverse images, tensor comparisons and normalized compositors exist
simultaneously for every scheme and every commutative condensed coefficient ring.

Source: the maps-used sentence of `fix-prop-coherence.proof.md`; Stacks 03D2, 03D8,
03EL, 0G7E and 07A4 (blueprint: lem-pur-diagram-geometric-tensor-presentations).

Proof: the coefficient comparison for `p_X^* Λ` is invertible. Thus the native module
inverse image is exact, and its specified adjunction gives preservation of colimits.
The exact-derived comparison identifies its total left derived functor with termwise
pullback. Geometric inverse image preserves K-flat complexes; extension of scalars along
the coefficient isomorphism is an equivalence and also preserves them. The canonical
bivariately derived tensor comparison is invertible and its defining counit equation is
the representative normalization. On underlying sheaves the module direct-image compositor
is precisely the geometric sheaf compositor. Conjugation gives its inverse-image mate,
and the unit equation for conjugate transformations gives the equality of the two unit
routes. These statements hold before any finite reduction or constructible restriction. -/
theorem diagramGeometricTensorPresentations : GeometricTensorPresentations Λ where
  coefficient _ := inferInstance
  limits _ := inferInstance
  colimits _ := inferInstance
  adjunction f := ⟨upperStarLowerStarAdjunction Λ f⟩
  derived f := (upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory_hom_fac
  resolving f _ hP := kFlat_upperStar_mapHomologicalComplex_obj Λ f hP
  tensor _ := inferInstance
  normalized f := leftDerivedUpperStarTensor_fac Λ f
  sections f g M := lowerStarComp_hom_app_hom Λ f g M
  mate f g := conjugateIsoEquiv_upperStarComp Λ f g
  unit f g M := upperStarLowerStarAdjunction_unit_app_upperStarComp Λ f g M

end AlgebraicGeometry.ProEtale.CondensedRing
