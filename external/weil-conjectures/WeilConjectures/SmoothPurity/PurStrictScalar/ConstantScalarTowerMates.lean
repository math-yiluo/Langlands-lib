/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.ConstantScalarTowerAdjunction
import all WeilConjectures.CategoryTheory.ExactDerivedSquare.DerivedExactSquareCoherence

/-! # Finite scalar mates on strict compact-support towers

Source: Stacks Project, Tags 07A6, 0B56, 0940 and 0E8I; auxiliary extracted from
compact-support coefficient comparison, Steps 3--4.
(blueprint: def-pur-constant-scalar-tower-mates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a b c d va vb vc vd wa wb wc wd
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

/-- The canonical cochain form of the right-derived unit.
Source: Stacks 0D6E (blueprint: def-pur-constant-scalar-tower-mates). -/
def derivedUnit {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
    [Abelian.HasKInjectiveResolutions A]
    (H : A ⥤ B) [H.Additive] (K : CochainComplex A ℤ) :
    DerivedCategory.Q.obj ((H.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      H.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso B).inv.app _ ≫
    H.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) ≫
    H.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso A).hom.app K)

/-- The whole-cochain unit normalization of a square with exact vertical functors.
This is an equation on all complexes, before any finite diagram evaluation.
Source: Stacks 0D6E (blueprint: def-pur-constant-scalar-tower-mates). -/
def unitCompatible
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
    [HasDerivedCategory.{wc} C] [HasDerivedCategory.{wd} D]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
    (H : A ⥤ B) (G : C ⥤ D) (V : A ⥤ C) (W : B ⥤ D)
    [hAdd : H.Additive] [gAdd : G.Additive] [vAdd : V.Additive] [wAdd : W.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (α : H ⋙ W ≅ V ⋙ G)
    (δ : H.rightDerivedFunctor ⋙ W.mapDerivedCategory ≅
      V.mapDerivedCategory ⋙ G.rightDerivedFunctor) : Prop :=
  ∀ P : CochainComplex A ℤ,
    W.mapDerivedCategory.map (derivedUnit H P) ≫
        δ.hom.app (DerivedCategory.Q.obj P) ≫
        G.rightDerivedFunctor.map (V.mapDerivedCategoryFactors.hom.app P) =
      W.mapDerivedCategoryFactors.hom.app
          ((H.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex α (.up ℤ)).hom.app P) ≫
        derivedUnit G ((V.mapHomologicalComplex (.up ℤ)).obj P)

attribute [local irreducible] unitCompatible derivedUnit

private theorem unitCompatible_existsUnique
    {A B C D : Type (a + 1)}
    [Category.{a} A] [Category.{a} B] [Category.{a} C] [Category.{a} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wa} B]
    [HasDerivedCategory.{wa} C] [HasDerivedCategory.{wa} D]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
    (H : A ⥤ B) (G : C ⥤ D) (V : A ⥤ C) (W : B ⥤ D)
    [H.Additive] [G.Additive] [V.Additive] [W.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    [V.PreservesKInjectiveComplexes] (α : H ⋙ W ≅ V ⋙ G) :
    ∃! δ : H.rightDerivedFunctor ⋙ W.mapDerivedCategory ≅
        V.mapDerivedCategory ⋙ G.rightDerivedFunctor,
      unitCompatible H G V W α δ := by
  obtain ⟨δ, hδ⟩ := CategoryTheory.ExactDerivedSquare.square_exists H G V W α (by
    intro I hI
    have := hI
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance)
  refine ⟨δ, ?_, ?_⟩
  · simpa only [unitCompatible, derivedUnit, Functor.rightDerivedFunctorUnitQ,
      NatIso.mapHomologicalComplex] using hδ
  · intro δ' hδ'
    apply CategoryTheory.ExactDerivedSquare.square_unique H G V W α δ' δ ?_ hδ
    simpa only [unitCompatible, derivedUnit, Functor.rightDerivedFunctorUnitQ,
      NatIso.mapHomologicalComplex] using hδ'

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- The ordinary proper restriction comparison is uniquely identity on all
underlying tower sections, including transitions.
Source: Stacks 03DA, 0D6E (blueprint: def-pur-constant-scalar-tower-mates).
Proof: the recorded ordinary restriction/direct-image square is identity on
sections of N over the same base-change object. Postcompose this square on
strict diagrams. The coefficient square identifies the scalar actions. Identity
is natural, invertible, and uniquely determines every component sheaf map. -/
theorem properRestrictionOrdinary_existsUnique {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ∃! d : towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g ⋙
          restrict l E F i Y ≅
        restrict l E F i X ⋙
          towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g,
      ∀ (N : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) X)
        (n : ℕ) (V : Y.ProEtᵒᵖ),
        HEq (fun x : (N.obj (op n)).val.obj ((proEtaleBaseChange g).op.obj V) ↦
            (((d.hom.app N).app (op n)).val.app V) x)
          (id : (N.obj (op n)).val.obj ((proEtaleBaseChange g).op.obj V) →
            (N.obj (op n)).val.obj ((proEtaleBaseChange g).op.obj V)) := by
  classical
  obtain ⟨e, he, -⟩ := proEtaleRingRestrictionDirectImage_existsUnique g
    (coefficients (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Y)
    (coefficients (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) Y)
    (coefficients (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X)
    (coefficients (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) X)
    (constantMap l E F i Y) (constantMap l E F i X)
    (constantRingIso (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
    (constantRingIso (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g)
    ((change l E F i).square g)
  let d : towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g ⋙
          restrict l E F i Y ≅
        restrict l E F i X ⋙
          towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g :=
    NatIso.ofComponents (fun N ↦ NatIso.ofComponents (fun n ↦ e.app (N.obj n))
      (fun f ↦ e.hom.naturality (N.map f))) (by
        intro N M f
        apply NatTrans.ext
        funext n
        exact e.hom.naturality (f.app n))
  have hd : ∀ (N : Towers
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) X)
      (n : ℕ) (V : Y.ProEtᵒᵖ),
      HEq (fun x ↦ (((d.hom.app N).app (op n)).val.app V) x)
        (id : (N.obj (op n)).val.obj ((proEtaleBaseChange g).op.obj V) →
          (N.obj (op n)).val.obj ((proEtaleBaseChange g).op.obj V)) := by
    intro N n V
    exact heq_of_eq (funext (he (N.obj (op n)) V))
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply NatTrans.ext
  funext n
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (congrFun (eq_of_heq (hd' N (unop n) V)) x).trans
    (congrFun (eq_of_heq (hd N (unop n) V)) x).symm

/-- The uniquely specified ordinary restriction/proper-image square on strict towers.
Source: Stacks 0D6E (blueprint: def-pur-constant-scalar-tower-mates). -/
def properRestrictionOrdinary {X Y : Scheme.{u}} (g : X ⟶ Y) :
    towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g ⋙
        restrict l E F i Y ≅
      restrict l E F i X ⋙
        towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g :=
  (properRestrictionOrdinary_existsUnique l E F i g).choose

/-- Restriction/direct image has a unique comparison with the canonical whole-complex
resolution units and the identity-on-sections ordinary square.
Source: Stacks 0D6E (blueprint: def-pur-constant-scalar-tower-mates).
Proof: finite free tensor is an exact left adjoint of restriction, hence restriction
preserves K-injectives. Derive the ordinary identity square on simultaneous tower
resolutions. The canonical derived-composite comparisons give an isomorphism
satisfying the displayed equation. The universal property of the derived composite
determines it uniquely from this equation on every complex. -/
theorem properRestriction_existsUnique {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ∃! d : R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g ⋙ U l E F i Y ≅
        U l E F i X ⋙ R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g,
      unitCompatible
        (towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g)
        (towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
        (restrict l E F i X) (restrict l E F i Y)
        (properRestrictionOrdinary l E F i g) d := by
  have hlim := (tensor_exact l E F i X).1
  have hcolim := (tensor_exact l E F i X).2
  have adj : tensor l E F i X ⊣ restrict l E F i X :=
    (pbcScalarAdjunction (constantMap l E F i X)).whiskerRight ℕᵒᵖ
  have hkinj : (restrict l E F i X).PreservesKInjectiveComplexes :=
    adj.preservesKInjectiveComplexes
  exact unitCompatible_existsUnique
    (towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g)
    (towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
    (restrict l E F i X) (restrict l E F i Y)
    (properRestrictionOrdinary l E F i g)

/-- The proper restriction comparison determined by the actual ordinary square and
canonical whole-cochain units, before finite evaluation.
Source: Stacks 0D6E (blueprint: def-pur-constant-scalar-tower-mates). -/
def properRestriction {X Y : Scheme.{u}} (g : X ⟶ Y) :
    R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g ⋙ U l E F i Y ≅
      U l E F i X ⋙ R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g :=
  (properRestriction_existsUnique l E F i g).choose

/-- The canonical proper scalar mate, with its B action retained.
Source: Stacks 07A6, 0B56 (blueprint: def-pur-constant-scalar-tower-mates). -/
def proper {X Y : Scheme.{u}} (g : X ⟶ Y) :
    R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g ⋙ T l E F i Y ⟶
      T l E F i X ⋙ R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g :=
  ((mateEquiv (scalarAdj l E F i X) (scalarAdj l E F i Y)).symm
    (TwoSquare.mk _ _ _ _ (properRestriction l E F i g).inv))

/-- The open restriction square on strict towers is the actual ordinary open mate.
Source: Stacks 0E8I (blueprint: def-pur-constant-scalar-tower-mates). -/
def openRestrictionOrdinary {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    restrict l E F i X ⋙
        towerJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j ≅
      towerJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) j ⋙
        restrict l E F i Y :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
    (asIso (PurCompactSupport.openRestrictionMap (change l E F i) j))

/-- Exact localization fixes the open square on the entire diagram category.
Source: Stacks 0E8I (blueprint: def-pur-constant-scalar-tower-mates). -/
def openRestriction {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    U l E F i X ⋙ J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j ≅
      J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) j ⋙ U l E F i Y :=
  Functor.mapDerivedCategorySquareIso (openRestrictionOrdinary l E F i j)

/-- Open scalar tensor balancing is the scalar-adjunction mate of the open square.
Source: Stacks 0E8I, 07A6 (blueprint: def-pur-constant-scalar-tower-mates). -/
def openTensor {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j ⋙ T l E F i Y ⟶
      T l E F i X ⋙ J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) j :=
  ((mateEquiv (scalarAdj l E F i X) (scalarAdj l E F i Y)).symm
    (TwoSquare.mk _ _ _ _ (openRestriction l E F i j).hom))

/-- The proper/open functor on constant integral towers, deriving the proper part
separately after exact open extension.
Source: Stacks 0940 (blueprint: def-pur-constant-scalar-tower-mates). -/
def image {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) c.i ⋙
    R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) c.g

/-- The ordered proper mate followed by proper image of open tensor balancing.
Source: Stacks 07A6, 0E8I (blueprint: def-pur-constant-scalar-tower-mates). -/
def comparison {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    image l E c ⋙ T l E F i Y ⟶ T l E F i X ⋙ image l F c :=
  Functor.whiskerLeft
      (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) c.i)
      (proper l E F i c.g) ≫
    Functor.whiskerRight (openTensor l E F i c.i)
      (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) c.g)

end WeilConjectures.PurStrictScalar
