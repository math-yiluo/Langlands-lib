/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction

/-! # Transport of the normalized scalar tensor comparison

Source: Stacks Project, Tags 06YY and 0D6D.
-/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v u w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures SheafOfModules

namespace WeilConjectures.ScalarTensorTransport
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [∀ R : Sheaf J CommRingCat.{max c v u}, HasDerivedCategory.{w} (scalarModules J R)]
  {R S : Sheaf J CommRingCat.{max c v u}} (a : R ⟶ S)

private theorem extension_eq (A : ScalarDerivedPair.{c, v, max c v u, w} (J := J) a)
    (E : scalarModules J R ⥤ scalarModules J S)
    (hobj : ∀ P, E.obj P = changeOfRings a P)
    (hmap : ∀ {P Q} (f : P ⟶ Q), E.map f = eqToHom (hobj P) ≫
      changeOfRingsHom a P f ≫ eqToHom (hobj Q).symm) : A.extension = E := by
  refine CategoryTheory.Functor.ext (fun P ↦ (A.extension_obj P).trans (hobj P).symm) ?_
  intro P Q f
  rw [A.extension_map, hmap]
  simp

private noncomputable def derivedIso (A : ScalarDerivedPair.{c, v, max c v u, w} (J := J) a)
    (F : DerivedCategory (scalarModules J R) ⥤ DerivedCategory (scalarModules J S))
    (ε : DerivedCategory.Qh ⋙ F ⟶
      scalarHomotopy.{c, v, max c v u} A.extension A.extension_additive ⋙ DerivedCategory.Qh)
    [F.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (scalarModules J R) (.up ℤ))] :
    A.derived ≅ F :=
  letI := A.isLeftDerived
  Functor.leftDerivedNatIso A.derived F A.counit ε
    (HomotopyCategory.quasiIso (scalarModules J R) (.up ℤ)) (Iso.refl _)

private theorem counit_square
    {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (e : F ≅ G) {X Y : C} {Z W : D} (s : X ⟶ Y) (t : W ⟶ Z)
    (p : F.obj Y ⟶ W) (q : G.obj Y ⟶ W)
    (h : e.hom.app Y ≫ q = p) :
    e.hom.app X ≫ G.map s ≫ q ≫ t = F.map s ≫ p ≫ t := by
  rw [← e.hom.naturality_assoc, reassoc_of% h]

private theorem derivedIso_complex (A : ScalarDerivedPair.{c, v, max c v u, w} (J := J) a)
    (F : DerivedCategory (scalarModules J R) ⥤ DerivedCategory (scalarModules J S))
    (ε : DerivedCategory.Qh ⋙ F ⟶
      scalarHomotopy.{c, v, max c v u} A.extension A.extension_additive ⋙ DerivedCategory.Qh)
    [F.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (scalarModules J R) (.up ℤ))]
    (P : CochainComplex (scalarModules J R) ℤ) :
    (derivedIso.{c, v, u, w} J a A F ε).hom.app (DerivedCategory.Q.obj P) ≫
        scalarPairComplexComparison.{c, v, max c v u, w} A.extension A.extension_additive F ε P =
      scalarPairComplexComparison.{c, v, max c v u, w}
        A.extension A.extension_additive A.derived A.counit P := by
  let := A.isLeftDerived
  dsimp only [scalarPairComplexComparison]
  apply counit_square (derivedIso.{c, v, u, w} J a A F ε)
  have h := Functor.leftDerivedNatTrans_app A.derived F A.counit ε
    (HomotopyCategory.quasiIso (scalarModules J R) (.up ℤ)) (𝟙 _)
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  change (derivedIso.{c, v, u, w} J a A F ε).hom.app _ ≫ ε.app _ =
    A.counit.app _ ≫ 𝟙 _ at h
  exact h.trans (Category.comp_id _)

private noncomputable def transportTensorIso
    {C D : Type*} [Category* C] [Category* D]
    (T : C × C ⥤ C) (U : D × D ⥤ D) {F G : C ⥤ D}
    (e : F ≅ G) (μ : T ⋙ F ≅ F.prod F ⋙ U) : T ⋙ G ≅ G.prod G ⋙ U :=
  Functor.isoWhiskerLeft T e.symm ≪≫ μ ≪≫ Functor.isoWhiskerRight (NatIso.prod e e) U

private theorem transportTensorIso_square
    {C D : Type*} [Category* C] [Category* D]
    (T : C × C ⥤ C) (U : D × D ⥤ D) {F G : C ⥤ D}
    (e : F ≅ G) (μ : T ⋙ F ≅ F.prod F ⋙ U)
    {A K L : C} (s : A ⟶ T.obj (K, L))
    {K' L' N : D} (p : F.obj K ⟶ K') (q : F.obj L ⟶ L')
    (p' : G.obj K ⟶ K') (q' : G.obj L ⟶ L')
    (r : F.obj A ⟶ N) (r' : G.obj A ⟶ N) (f : N ⟶ U.obj (K', L'))
    (hp : e.hom.app K ≫ p' = p) (hq : e.hom.app L ≫ q' = q)
    (hr : e.hom.app A ≫ r' = r)
    (h : F.map s ≫ μ.hom.app (K, L) ≫
      U.map (X := (F.obj K, F.obj L)) (Y := (K', L')) (p, q) = r ≫ f) :
    G.map s ≫ (transportTensorIso T U e μ).hom.app (K, L) ≫
        U.map (X := (G.obj K, G.obj L)) (Y := (K', L')) (p', q') =
      r' ≫ f := by
  change G.map s ≫ (e.inv.app (T.obj (K, L)) ≫ μ.hom.app (K, L) ≫
    U.map (X := (F.obj K, F.obj L)) (Y := (G.obj K, G.obj L))
      (e.hom.app K, e.hom.app L)) ≫ U.map (X := (G.obj K, G.obj L)) (Y := (K', L')) (p', q') = _
  simp only [Category.assoc]
  rw [e.inv.naturality_assoc, ← U.map_comp]
  change e.inv.app A ≫ F.map s ≫ μ.hom.app (K, L) ≫
    U.map (X := (F.obj K, F.obj L)) (Y := (K', L'))
      (e.hom.app K ≫ p', e.hom.app L ≫ q') = _
  rw [hp, hq, h, ← hr]
  simp

attribute [local irreducible] derivedInternalHomOfUniverses homComplexFunctor
  coefficientTotalTensor CoefficientClosedStructure.tensor CoefficientTensorModels.iso
  coefficientTensorGenerator scalarPairComplexComparison
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The scalar unit on a fixed degree of a complex, with its extension carrier exposed.
Source: Stacks 06YY (blueprint: lem-sf-scalar-tensor-comparison-transport). -/
noncomputable def fixedScalarComplexUnitSection
    (E : scalarModules J R ⥤ scalarModules J S) (hadd : E.Additive)
    (eta : 𝟭 (scalarModules J R) ⟶ E ⋙ scalarRestriction.{c, v, max c v u} a)
    (P : CochainComplex (scalarModules J R) ℤ) (k : ℤ) (V : Cᵒᵖ)
    (x : (P.X k).val.obj V) :
    (((scalarComplex.{c, v, max c v u} E hadd).obj P).X k).val.obj V :=
  (eta.app (P.X k)).val.app V x

attribute [local irreducible] fixedScalarComplexUnitSection

/-- Scalar tensor data for a prescribed ordinary and universal derived pair.
Source: Stacks 06YY and 0D6D
(blueprint: lem-sf-scalar-tensor-comparison-transport). -/
structure FixedScalarTensorComparison
    (M : ScalarHomModels.{c, v, u, w} J)
    (E : scalarModules J R ⥤ scalarModules J S) (hadd : E.Additive)
    (hobj : ∀ P, E.obj P = changeOfRings a P)
    (F : DerivedCategory (scalarModules J R) ⥤ DerivedCategory (scalarModules J S))
    (ε : DerivedCategory.Qh ⋙ F ⟶
      scalarHomotopy.{c, v, max c v u} E hadd ⋙ DerivedCategory.Qh) where
  unit : 𝟭 (scalarModules J R) ⟶ E ⋙ scalarRestriction.{c, v, max c v u} a
  unit_normalize : ∀ (P : scalarModules J R) (V : Cᵒᵖ) (x : P.val.obj V),
    (eqToHom (hobj P)).val.app V ((unit.app P).val.app V x) =
      (toSheafify J (changeOfRingsPresheaf a P).presheaf).app V
        ((ModuleCat.extendRestrictScalarsAdj (a.hom.app V).hom).unit.app (P.val.obj V) x)

  /-- Scalar extension carries K-flat complexes to K-flat complexes. -/
  preservesKFlat : ∀ (P : CochainComplex (scalarModules J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
        ((scalarComplex.{c, v, max c v u} E hadd).obj P)
  /-- The actual chain tensor comparison, with the differential signs retained. -/
  complexIso : ∀ (P Q : CochainComplex (scalarModules J R) ℤ),
    (scalarComplex.{c, v, max c v u} E hadd).obj
        ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) ≅
      (coefficientTotalTensor.{u, c, v} J S).obj
        ((scalarComplex.{c, v, max c v u} E hadd).obj P,
         (scalarComplex.{c, v, max c v u} E hadd).obj Q)
  /-- It sends 1 tensor (x tensor y) to (1 tensor x) tensor (1 tensor y). -/
  generators : ∀ (P Q : CochainComplex (scalarModules J R) ℤ)
    (p q k : ℤ) (h : p + q = k) (V : Cᵒᵖ)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
    ((complexIso P Q).hom.f k).val.app V
        (fixedScalarComplexUnitSection.{c, v, u} J a E hadd unit
          ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) k V
          (coefficientTensorGenerator.{u, c, v} J R P Q p q k h V x y)) =
      coefficientTensorGenerator.{u, c, v} J S
        ((scalarComplex.{c, v, max c v u} E hadd).obj P)
        ((scalarComplex.{c, v, max c v u} E hadd).obj Q)
        p q k h V (fixedScalarComplexUnitSection.{c, v, u} J a E hadd unit P p V x)
          (fixedScalarComplexUnitSection.{c, v, u} J a E hadd unit Q q V y)
  /-- The natural derived strong tensor comparison. -/
  iso : (M.closed R).tensor ⋙ F ≅
    (F.prod F) ⋙ (M.closed S).tensor
  /-- Its defining square on the actual K-flat representatives. -/
  normalization : ∀ (P Q : CochainComplex (scalarModules J R) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q),
    F.map
        ((CoefficientTensorModels.iso.{u, c, v, w} J R (M.closed R) (M.model R)
          P Q hp hq).hom) ≫
      iso.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (M.closed S).tensor.map (Prod.mkHom
          (scalarPairComplexComparison.{c, v, max c v u, w} E hadd
            F ε P)
          (scalarPairComplexComparison.{c, v, max c v u, w} E hadd
            F ε Q)) =
      scalarPairComplexComparison.{c, v, max c v u, w} E hadd
          F ε
            ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) ≫
        DerivedCategory.Q.map (complexIso P Q).hom ≫
          (CoefficientTensorModels.iso.{u, c, v, w} J S (M.closed S) (M.model S)
            _ _ (preservesKFlat P hp) (preservesKFlat Q hq)).hom

/-- Normalized scalar tensor data transport to any presentation of the same derived pair.
Source: Stacks 06YY and 0D6D
(blueprint: lem-sf-scalar-tensor-comparison-transport).

Proof: the equality of ordinary extensions identifies their chain tensors and
ordinary units. The left-derived universal property gives the unique natural
isomorphism of derived extensions commuting with counits. Conjugate the generic
strong tensor comparison by that isomorphism, on the output and on each input.
Its compatibility with the complex comparison follows from counit compatibility
and naturality at the quotient comparison. Substitution in the generic tensor
normalization square and cancellation of inverse isomorphisms proves the desired
square. Ordinary generators and preservation of K-flatness are unchanged under
the equality of ordinary extensions. -/
theorem fixedScalarTensorComparison_exists
    (M : ScalarHomModels.{c, v, u, w} J)
    (μ : ScalarHomTensorComparison.{c, v, u, w} M a)
    (E : scalarModules J R ⥤ scalarModules J S) (hadd : E.Additive)
    (hobj : ∀ P, E.obj P = changeOfRings a P)
    (he : (M.scalar a).extension = E)
    (F : DerivedCategory (scalarModules J R) ⥤ DerivedCategory (scalarModules J S))
    (ε : DerivedCategory.Qh ⋙ F ⟶
      scalarHomotopy.{c, v, max c v u} E hadd ⋙ DerivedCategory.Qh)
    (hF : F.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (scalarModules J R) (.up ℤ))) :
    Nonempty (FixedScalarTensorComparison.{c, v, u, w} J a M E hadd hobj F ε) := by
  let := hF
  subst E
  let e := derivedIso.{c, v, u, w} J a (M.scalar a) F ε
  refine ⟨{
    unit := (M.scalar a).ordinaryAdjunction.unit
    unit_normalize := ?_
    preservesKFlat := μ.preservesKFlat
    complexIso := μ.complexIso
    generators := by
      simpa only [fixedScalarComplexUnitSection, scalarHomUnitSection] using μ.generators
    iso := transportTensorIso (M.closed R).tensor (M.closed S).tensor e μ.iso
    normalization := ?_ }⟩
  · exact (M.scalar a).ordinaryUnit
  · intro P Q hp hq
    apply transportTensorIso_square (M.closed R).tensor (M.closed S).tensor e μ.iso
      ((CoefficientTensorModels.iso.{u, c, v, w} J R (M.closed R) (M.model R)
        P Q hp hq).hom)
    · exact derivedIso_complex.{c, v, u, w} J a (M.scalar a) F ε P
    · exact derivedIso_complex.{c, v, u, w} J a (M.scalar a) F ε Q
    · exact derivedIso_complex.{c, v, u, w} J a (M.scalar a) F ε _
    · exact μ.normalization P Q hp hq

end WeilConjectures.ScalarTensorTransport
