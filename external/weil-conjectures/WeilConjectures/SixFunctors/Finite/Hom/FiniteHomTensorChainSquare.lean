/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientSystemScalarCalculus
public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

/-! # General proof tools for the intrinsic scalar tensor composition square

Source: blueprint lemma-change-coefficients-internal-hom--1, successive quotient paragraph.
The public chain square is the generator calculation used before localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u a₁ b₁ v₁ v₂ w₁ w₂
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

open CategoryTheory.Functor CategoryTheory.Limits Opposite

attribute [local irreducible] constantSheaf
attribute [local irreducible] CoefficientClosedStructure.tensor
  SheafOfModules.monoidalCategory coefficientTotalTensor coefficientTensorGenerator
  DerivedCategory _root_.instCategoryDerivedCategory DerivedCategory.Q DerivedCategory.Qh
  HasDerivedCategory.standard SheafOfModules.instPreadditive

private theorem q_iso_of_quasi
    {A : Type a₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
    {P Q : CochainComplex A ℤ} (f : P ⟶ Q) (hf : QuasiIso f) :
    IsIso (DerivedCategory.Q.map f) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso A f).2 hf

private theorem representatives_of_resolution
    {A : Type a₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
    (W : ObjectProperty (CochainComplex A ℤ))
    (resolve : ∀ P : CochainComplex A ℤ,
      ∃ P' : CochainComplex A ℤ, ∃ f : P' ⟶ P, W P' ∧ QuasiIso f)
    (Y : DerivedCategory A) :
    ∃ P : CochainComplex A ℤ, W P ∧ Nonempty (DerivedCategory.Q.obj P ≅ Y) := by
  obtain ⟨P, p, hp, hq⟩ := resolve (DerivedCategory.Q.objPreimage Y)
  let _ : IsIso (DerivedCategory.Q.map p) := q_iso_of_quasi p hq
  exact ⟨P, hp, ⟨asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso Y⟩⟩

private theorem natTrans_app_eq_of_cover
    {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (a b : F ⟶ G) {P P' : A} (f : P' ⟶ P) (hf : IsIso (F.map f))
    (he : a.app P' = b.app P') : a.app P = b.app P := by
  let _ := hf
  apply (cancel_epi (F.map f)).mp
  rw [a.naturality, b.naturality, he]

private theorem tensor_square_descent
    {A B C P : Type*} [Category A] [Category B] [Category C]
    (T : A × A ⥤ A) (U : B × B ⥤ B) (V : C × C ⥤ C)
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    (μ : T ⋙ F ≅ F.prod F ⋙ U) (ν : U ⋙ G ≅ G.prod G ⋙ V)
    (ξ : T ⋙ H ≅ H.prod H ⋙ V) (α : F ⋙ G ≅ H)
    (q : P → A) (W : P → Prop)
    (rep : ∀ Y : A, ∃ p : P, W p ∧ Nonempty (q p ≅ Y))
    (eq : ∀ p p' : P, W p → W p' →
      G.map (μ.hom.app (q p, q p')) ≫ ν.hom.app (F.obj (q p), F.obj (q p')) ≫
        V.map (Prod.mkHom (α.hom.app (q p)) (α.hom.app (q p'))) =
      α.hom.app (T.obj (q p, q p')) ≫ ξ.hom.app (q p, q p'))
    (K M : A) :
    G.map (μ.hom.app (K, M)) ≫ ν.hom.app (F.obj K, F.obj M) ≫
      V.map (Prod.mkHom (α.hom.app K) (α.hom.app M)) =
    α.hom.app (T.obj (K, M)) ≫ ξ.hom.app (K, M) := by
  let lhs : T ⋙ F ⋙ G ⟶ H.prod H ⋙ V :=
    whiskerRight μ.hom G ≫ whiskerLeft (F.prod F) ν.hom ≫
      whiskerRight (NatTrans.prod α.hom α.hom) V
  let rhs : T ⋙ F ⋙ G ⟶ H.prod H ⋙ V := whiskerLeft T α.hom ≫ ξ.hom
  have he : lhs = rhs := by
    apply NatTrans.ext
    funext Y
    obtain ⟨p, hp, ⟨eP⟩⟩ := rep Y.1
    obtain ⟨p', hp', ⟨eQ⟩⟩ := rep Y.2
    exact natTrans_app_eq_of_cover lhs rhs (eP.prod eQ).hom
      (Iso.isIso_hom ((T ⋙ F ⋙ G).mapIso (eP.prod eQ))) (eq p p' hp hp')
  exact congrArg (fun z ↦ z.app (K, M)) he

private theorem normalized_unit_extension
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (Q : A ⥤ D) (Q' : B ⥤ E) (F : A ⥤ B) (U : B ⥤ A)
    (L : D ⥤ E) (R : E ⥤ D) (a : F ⊣ U) (d : L ⊣ R)
    (e : Q ⋙ L ⟶ F ⋙ Q') (ρ : Q' ⋙ R ≅ U ⋙ Q)
    (W : ObjectProperty A)
    (cover : ∀ P : A, ∃ P' : A, ∃ f : P' ⟶ P, W P' ∧ IsIso (Q.map f))
    (model : ∀ P : A, W P →
      d.unit.app (Q.obj P) ≫ R.map (e.app P) ≫ ρ.hom.app (F.obj P) =
        Q.map (a.unit.app P)) (P : A) :
    d.unit.app (Q.obj P) ≫ R.map (e.app P) ≫ ρ.hom.app (F.obj P) =
      Q.map (a.unit.app P) := by
  let lhs : Q ⟶ F ⋙ U ⋙ Q :=
    whiskerLeft Q d.unit ≫ whiskerRight e R ≫ whiskerLeft F ρ.hom
  let rhs : Q ⟶ F ⋙ U ⋙ Q := whiskerRight a.unit Q
  obtain ⟨P', f, hp, hf⟩ := cover P
  exact natTrans_app_eq_of_cover lhs rhs f hf (model P' hp)

private theorem map_iso_paste
    {A B : Type*} [Category A] [Category B] (Q : A ⥤ B)
    {X Y Z : A} (u : X ⟶ Z) (e : Y ≅ Z)
    {P T : B} (x : Q.obj Z ⟶ P) (y : P ⟶ T) :
    Q.map u ≫ x ≫ y = Q.map (u ≫ e.inv) ≫ (Q.map e.hom ≫ x) ≫ y := by
  rw [Q.map_comp]
  simp only [Category.assoc]
  rw [← Q.map_comp_assoc e.inv e.hom, e.inv_hom_id, Q.map_id, Category.id_comp]

private theorem map_three_comp_eq
    {A B : Type*} [Category A] [Category B] (Q : A ⥤ B)
    {X Y Z T N : A} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ N}
    {a : X ⟶ T} {b : T ⟶ N} (w : f ≫ g ≫ h = a ≫ b) :
    Q.map f ≫ Q.map g ≫ Q.map h = Q.map a ≫ Q.map b := by
  simpa only [Functor.map_comp] using congrArg Q.map w

private theorem leftComp_unit
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R : B ⥤ A} {L' : B ⥤ C} {R' : C ⥤ B}
    {L'' : A ⥤ C} {R'' : C ⥤ A}
    (a : L ⊣ R) (b : L' ⊣ R') (c : L'' ⊣ R'') (η : R' ⋙ R ≅ R'') (M : A) :
    (a.comp b).homEquiv M _ ((Adjunction.leftAdjointCompIso a b c η).hom.app M) =
      c.unit.app M ≫ η.inv.app (L''.obj M) := by
  apply (Iso.eq_comp_inv (η.app (L''.obj M))).2
  change (a.comp b).homEquiv M _ _ ≫ η.hom.app _ = _
  rw [Adjunction.homEquiv_unit, Category.assoc, η.hom.naturality, ← Category.assoc]
  have hu := unit_conjugateEquiv (a.comp b) c
    (Adjunction.leftAdjointCompIso a b c η).inv M
  rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv] at hu
  rw [hu, Category.assoc, ← R''.map_comp, Iso.inv_hom_id_app, R''.map_id]
  exact Category.comp_id _

private theorem leftComp_transpose
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R : B ⥤ A} {L' : B ⥤ C} {R' : C ⥤ B}
    {L'' : A ⥤ C} {R'' : C ⥤ A}
    (a : L ⊣ R) (b : L' ⊣ R') (c : L'' ⊣ R'') (η : R' ⋙ R ≅ R'')
    (M : A) (N : C) (f : L''.obj M ⟶ N) :
    (a.comp b).homEquiv M N
        ((Adjunction.leftAdjointCompIso a b c η).hom.app M ≫ f) =
      c.homEquiv M N f ≫ η.inv.app N := by
  rw [(a.comp b).homEquiv_naturality_right, leftComp_unit, Category.assoc,
    ← η.inv.naturality, ← Category.assoc, c.homEquiv_unit]

/-- Localization of a specified counit comparison through the fixed quotient functors.
This is the literal four-arrow composite used by the finite scalar models.
Source: blueprint lemma-change-coefficients-internal-hom--1, representative normalization. -/
def finiteHomTensorRepresentativeComparison
    {A : Type a₁} {B : Type b₁} [Category.{v₁} A] [Abelian A]
    [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (E : A ⥤ B) [E.Additive] (F : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ F ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ F ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  whiskerRight (DerivedCategory.quotientCompQhIso _).inv F ≫
    whiskerLeft (HomotopyCategory.quotient _ (.up ℤ)) ε ≫
    whiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
    whiskerLeft (E.mapHomologicalComplex (.up ℤ)) (DerivedCategory.quotientCompQhIso _).hom

private theorem representativeComparison_model
    {A : Type a₁} {B : Type b₁} [Category.{v₁} A] [Abelian A]
    [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (E : A ⥤ B) [E.Additive] (F : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ F ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex A ℤ)
    (hp : IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) :
    (finiteHomTensorRepresentativeComparison E F ε).app P =
      (coefficientLocalizedCounitModel F P ((E.mapHomologicalComplex (.up ℤ)).obj P)
        (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) hp).hom := by
  change _ ≫ _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ _ = _
  erw [DerivedCategory.Qh.map_id, Category.id_comp]
  rfl

attribute [local irreducible] finiteHomTensorRepresentativeComparison
  coefficientLocalizedCounitModel

private theorem restrictionComp_inv_section
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (q : R ⟶ T)
    (h : f ≫ g = q) (M : SheafOfModules.{u} T) (V : Cᵒᵖ) (x : M.val.obj V) :
    (((normalizedDVRRestrictionCompIso f g ≪≫
      eqToIso (congrArg (fun z ↦ SheafOfModules.restrictScalars.{u} z) h)).inv.app M).val.app V)
        x = x := by
  cases h
  rfl

private def scalarUnitSection
    {C : Type a₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (f : R ⟶ S)
    {F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S}
    (d : F ⊣ SheafOfModules.restrictScalars f)
    (M : SheafOfModules.{u} R) (V : Cᵒᵖ) (x : M.val.obj V) :
    (F.obj M).val.obj V := (d.unit.app M).val.app V x

attribute [local irreducible] scalarUnitSection

/-- The termwise image of the ordinary left-adjoint composition mate.
Source: blueprint lemma-change-coefficients-internal-hom--1, successive quotients. -/
def finiteHomTensorComplexAssociator
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    {F : A ⥤ B} {U : B ⥤ A} {G : B ⥤ C} {V : C ⥤ B}
    {H : A ⥤ C} {W : C ⥤ A}
    [F.Additive] [G.Additive] [H.Additive] [U.Additive] [V.Additive] [W.Additive]
    (a : F ⊣ U) (b : G ⊣ V) (c : H ⊣ W) (e : V ⋙ U ≅ W) :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      H.mapHomologicalComplex (.up ℤ) :=
  mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ) ≪≫
    NatIso.mapHomologicalComplex (Adjunction.leftAdjointCompIso a b c e) (.up ℤ)

private theorem complexAssoc_transpose
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    {F : A ⥤ B} {U : B ⥤ A} {G : B ⥤ C} {V : C ⥤ B}
    {H : A ⥤ C} {W : C ⥤ A}
    [F.Additive] [G.Additive] [H.Additive] [U.Additive] [V.Additive] [W.Additive]
    (a : F ⊣ U) (b : G ⊣ V) (c : H ⊣ W) (e : V ⋙ U ≅ W)
    (P : CochainComplex A ℤ) :
    ((a.mapHomologicalComplex (.up ℤ)).comp (b.mapHomologicalComplex (.up ℤ))).homEquiv _ _
        ((finiteHomTensorComplexAssociator a b c e).hom.app P) =
      (c.mapHomologicalComplex (.up ℤ)).unit.app P ≫
        (NatIso.mapHomologicalComplex e (.up ℤ)).inv.app
          ((H.mapHomologicalComplex (.up ℤ)).obj P) := by
  apply HomologicalComplex.Hom.ext
  funext i
  simp only [Adjunction.homEquiv_unit, Adjunction.comp_unit_app, HomologicalComplex.comp_f,
    Functor.comp_map, Functor.mapHomologicalComplex_map_f]
  change (a.unit.app (P.X i) ≫ U.map (b.unit.app (F.obj (P.X i)))) ≫
    U.map (V.map (𝟙 _ ≫ (Adjunction.leftAdjointCompIso a b c e).hom.app (P.X i))) =
      c.unit.app (P.X i) ≫ e.inv.app _
  rw [Category.id_comp]
  simpa only [Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Functor.comp_map] using
    leftComp_unit a b c e (P.X i)

attribute [local irreducible] finiteHomTensorComplexAssociator

attribute [local semireducible] scalarUnitSection in
private theorem complexAssoc_unit_section
    {C : Type a₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {R S T : Sheaf J RingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (q : R ⟶ T)
    (hf : f ≫ g = q)
    {F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S}
    {G : SheafOfModules.{u} S ⥤ SheafOfModules.{u} T}
    {H : SheafOfModules.{u} R ⥤ SheafOfModules.{u} T}
    [F.Additive] [G.Additive] [H.Additive]
    (a : F ⊣ SheafOfModules.restrictScalars f)
    (b : G ⊣ SheafOfModules.restrictScalars g)
    (c : H ⊣ SheafOfModules.restrictScalars q)
    (P : CochainComplex (SheafOfModules.{u} R) ℤ)
    (i : ℤ) (V : Cᵒᵖ) (x : (P.X i).val.obj V) :
    ((HomologicalComplex.Hom.f
        ((finiteHomTensorComplexAssociator a b c (normalizedDVRRestrictionCompIso f g ≪≫
          eqToIso (congrArg (fun z ↦ SheafOfModules.restrictScalars.{u} z) hf))).hom.app P)
        i).val.app V)
      (scalarUnitSection g b _ V (scalarUnitSection f a _ V x)) =
      scalarUnitSection q c _ V x := by
  have hu := congrArg (fun z ↦ (z.f i).val.app V x)
    (complexAssoc_transpose a b c (normalizedDVRRestrictionCompIso f g ≪≫
      eqToIso (congrArg (fun z ↦ SheafOfModules.restrictScalars.{u} z) hf)) P)
  simp only [Adjunction.homEquiv_unit, Adjunction.comp_unit_app, HomologicalComplex.comp_f,
    Functor.comp_map, Functor.mapHomologicalComplex_map_f] at hu
  change _ = (((normalizedDVRRestrictionCompIso f g ≪≫
    eqToIso (congrArg (fun z ↦ SheafOfModules.restrictScalars.{u} z) hf)).inv.app _).val.app V)
      (scalarUnitSection q c _ V x) at hu
  exact hu.trans (restrictionComp_inv_section f g q hf _ V _)

attribute [local semireducible] scalarUnitSection in
private theorem total_scalar_unit_ext
    {C : Type a₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max a₁ v₁ u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max a₁ v₁ u}]
    {A B T : Sheaf J CommRingCat.{max a₁ v₁ u}}
    (f : (sheafCompose J
      (forget₂ CommRingCat.{max a₁ v₁ u} RingCat.{max a₁ v₁ u})).obj A ⟶
      (sheafCompose J
        (forget₂ CommRingCat.{max a₁ v₁ u} RingCat.{max a₁ v₁ u})).obj B)
    (g : (sheafCompose J
      (forget₂ CommRingCat.{max a₁ v₁ u} RingCat.{max a₁ v₁ u})).obj B ⟶
      (sheafCompose J
        (forget₂ CommRingCat.{max a₁ v₁ u} RingCat.{max a₁ v₁ u})).obj T)
    {F : SheafOfModules.scalarModules J A ⥤ SheafOfModules.scalarModules J B}
    {G : SheafOfModules.scalarModules J B ⥤ SheafOfModules.scalarModules J T}
    (a : F ⊣ SheafOfModules.restrictScalars f)
    (b : G ⊣ SheafOfModules.restrictScalars g)
    (P Q : CochainComplex (SheafOfModules.scalarModules J A) ℤ) (i : ℤ)
    {N : SheafOfModules.scalarModules J T}
    {s t : G.obj (F.obj (((coefficientTotalTensor.{u, a₁, v₁} J A).obj (P, Q)).X i)) ⟶ N}
    (hh : ∀ (p q : ℤ) (hi : p + q = i) (V : Cᵒᵖ)
      (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
      s.val.app V (scalarUnitSection g b _ V (scalarUnitSection f a _ V
        (coefficientTensorGenerator.{u, a₁, v₁} J A P Q p q i hi V x y))) =
      t.val.app V (scalarUnitSection g b _ V (scalarUnitSection f a _ V
        (coefficientTensorGenerator.{u, a₁, v₁} J A P Q p q i hi V x y)))) : s = t := by
  apply ((a.comp b).homEquiv _ _).injective
  apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{a₁, v₁, u}
    (J := J) (R := A) P Q i _
  intro p q hi V x y
  exact hh p q hi V x y

attribute [local semireducible] scalarUnitSection in
/-- The ordinary scalar tensor square, tested on total pure generators.
Source: blueprint lemma-change-coefficients-internal-hom--1, successive-quotient tensor square
(blueprint: lem-coef-finite-hom-tensor-chain-square).
Proof: apply the composite scalar adjunction in each degree. Pure generators detect
maps out of the total tensor. Naturality moves the second scalar unit through the
first tensor comparison. Apply the two generator formulas, tensor naturality, and
the unit equation for the prescribed associator. The direct generator formula then
identifies the other composite. -/
theorem finiteHomTensor_chainSquare
    {C : Type a₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max a₁ v₁ u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max a₁ v₁ u}]
    {A B T : Sheaf J CommRingCat.{max a₁ v₁ u}}
    (f : ((sheafCompose J
      (forget₂ CommRingCat.{max a₁ v₁ u} RingCat.{max a₁ v₁ u})).obj A) ⟶
      ((sheafCompose J
      (forget₂ CommRingCat.{max a₁ v₁ u} RingCat.{max a₁ v₁ u})).obj B))
    (g : ((sheafCompose J
      (forget₂ CommRingCat.{max a₁ v₁ u} RingCat.{max a₁ v₁ u})).obj B) ⟶
      ((sheafCompose J
      (forget₂ CommRingCat.{max a₁ v₁ u} RingCat.{max a₁ v₁ u})).obj T))
    (j : ((sheafCompose J
      (forget₂ CommRingCat.{max a₁ v₁ u} RingCat.{max a₁ v₁ u})).obj A) ⟶
      ((sheafCompose J
      (forget₂ CommRingCat.{max a₁ v₁ u} RingCat.{max a₁ v₁ u})).obj T))
    {F : SheafOfModules.scalarModules J A ⥤ SheafOfModules.scalarModules J B}
    {G : SheafOfModules.scalarModules J B ⥤ SheafOfModules.scalarModules J T}
    {H : SheafOfModules.scalarModules J A ⥤ SheafOfModules.scalarModules J T}
    [hFadd : F.Additive] [hGadd : G.Additive] [hHadd : H.Additive]
    (a : F ⊣ SheafOfModules.restrictScalars f)
    (b : G ⊣ SheafOfModules.restrictScalars g)
    (c : H ⊣ SheafOfModules.restrictScalars j)
    (α : F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ⟶
      H.mapHomologicalComplex (.up ℤ))
    (hα : ∀ (P : CochainComplex (SheafOfModules.scalarModules J A) ℤ)
      (i : ℤ) (V : Cᵒᵖ) (x : (P.X i).val.obj V),
      ((α.app P).f i).val.app V
        ((fun M V x ↦ (b.unit.app M).val.app V x) _ V
          ((fun M V x ↦ (a.unit.app M).val.app V x) _ V x)) =
          (fun M V x ↦ (c.unit.app M).val.app V x) _ V x)
    (P Q : CochainComplex (SheafOfModules.scalarModules J A) ℤ)
    (eF : (F.mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{u, a₁, v₁} J A).obj (P, Q)) ≅
      (coefficientTotalTensor.{u, a₁, v₁} J B).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P, (F.mapHomologicalComplex (.up ℤ)).obj Q))
    (eG : (G.mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{u, a₁, v₁} J B).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj P, (F.mapHomologicalComplex (.up ℤ)).obj Q)) ≅
      (coefficientTotalTensor.{u, a₁, v₁} J T).obj
        ((G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj P),
          (G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj Q)))
    (eH : (H.mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{u, a₁, v₁} J A).obj (P, Q)) ≅
      (coefficientTotalTensor.{u, a₁, v₁} J T).obj
        ((H.mapHomologicalComplex (.up ℤ)).obj P, (H.mapHomologicalComplex (.up ℤ)).obj Q))
    (hF : CoefficientScalarTensorGenerators.{u, a₁, v₁} J A B F
      ((fun M V x ↦ (a.unit.app M).val.app V x)) P Q eF)
    (hG : CoefficientScalarTensorGenerators.{u, a₁, v₁} J B T G
      ((fun M V x ↦ (b.unit.app M).val.app V x)) _ _ eG)
    (hH : CoefficientScalarTensorGenerators.{u, a₁, v₁} J A T H
      ((fun M V x ↦ (c.unit.app M).val.app V x)) P Q eH) :
    (G.mapHomologicalComplex (.up ℤ)).map eF.hom ≫ eG.hom ≫
      (coefficientTotalTensor.{u, a₁, v₁} J T).map
        (Prod.mkHom (α.app P) (α.app Q)) =
      α.app ((coefficientTotalTensor.{u, a₁, v₁} J A).obj (P, Q)) ≫ eH.hom := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply total_scalar_unit_ext.{u, a₁, v₁} f g a b P Q i
  intro p q hi V x y
  have hn (M N : SheafOfModules.scalarModules J B) (z : M ⟶ N) (x : M.val.obj V) :
      (G.map z).val.app V (scalarUnitSection g b M V x) =
        scalarUnitSection g b N V (z.val.app V x) :=
    (congrArg (fun z ↦ z.val.app V x) (b.unit.naturality z)).symm
  change (((coefficientTotalTensor.{u, a₁, v₁} J T).map
      (Prod.mkHom (α.app P) (α.app Q))).f i).val.app V
    ((eG.hom.f i).val.app V ((G.map (eF.hom.f i)).val.app V
      (scalarUnitSection g b _ V (scalarUnitSection f a _ V _)))) =
    (eH.hom.f i).val.app V (((α.app _).f i).val.app V
      (scalarUnitSection g b _ V (scalarUnitSection f a _ V _)))
  have hn' := hn _ _ (eF.hom.f i) (scalarUnitSection f a _ V
    (coefficientTensorGenerator.{u, a₁, v₁} J A P Q p q i hi V x y))
  have hf' := hF p q i hi V x y
  have hg' := hG p q i hi V (scalarUnitSection f a _ V x) (scalarUnitSection f a _ V y)
  have hm := CategoryTheory.ScalarHomTensor.tensor_generator_map.{a₁, v₁, u}
    (J := J) (R := T) (α.app P) (α.app Q) p q i hi V
    (scalarUnitSection g b _ V (scalarUnitSection f a _ V x))
    (scalarUnitSection g b _ V (scalarUnitSection f a _ V y))
  let mapT := fun w ↦ ((((coefficientTotalTensor.{u, a₁, v₁} J T).map
    (Prod.mkHom (α.app P) (α.app Q))).f i).val.app V) w
  calc
    _ = _ := congrArg (fun w ↦ mapT ((eG.hom.f i).val.app V w)) hn'
    _ = _ := congrArg (fun w ↦ mapT ((eG.hom.f i).val.app V
      (scalarUnitSection g b _ V w))) hf'
    _ = _ := congrArg mapT hg'
    _ = _ := hm
    _ = _ := congrArg₂ (fun xx yy ↦ coefficientTensorGenerator.{u, a₁, v₁} J T
      ((H.mapHomologicalComplex (.up ℤ)).obj P) ((H.mapHomologicalComplex (.up ℤ)).obj Q)
      p q i hi V xx yy) (hα P p V x) (hα Q q V y)
    _ = _ := (hH p q i hi V x y).symm
    _ = _ := congrArg (fun w ↦ (eH.hom.f i).val.app V w)
      (hα ((coefficientTotalTensor.{u, a₁, v₁} J A).obj (P, Q)) i V
        (coefficientTensorGenerator.{u, a₁, v₁} J A P Q p q i hi V x y)).symm

private theorem normalized_tensor_comparison_assoc
    {A B C DA DB DC : Type*}
    [Category A] [Category B] [Category C] [Category DA] [Category DB] [Category DC]
    {F : A ⥤ B} {R : B ⥤ A} {G : B ⥤ C} {S : C ⥤ B} {H : A ⥤ C} {U : C ⥤ A}
    {FD : DA ⥤ DB} {RD : DB ⥤ DA} {GD : DB ⥤ DC} {SD : DC ⥤ DB}
    {HD : DA ⥤ DC} {UD : DC ⥤ DA} {QA : A ⥤ DA} {QB : B ⥤ DB} {QC : C ⥤ DC}
    (a : F ⊣ R) (b : G ⊣ S) (c : H ⊣ U)
    (ad : FD ⊣ RD) (bd : GD ⊣ SD) (cd : HD ⊣ UD)
    (εF : QA ⋙ FD ⟶ F ⋙ QB) (εG : QB ⋙ GD ⟶ G ⋙ QC) (εH : QA ⋙ HD ⟶ H ⋙ QC)
    (ρF : R ⋙ QA ⟶ QB ⋙ RD) (ρG : S ⋙ QB ⟶ QC ⋙ SD) (ρH : U ⋙ QA ⟶ QC ⋙ UD)
    (hF : ∀ P K (f : F.obj P ⟶ K),
      ad.homEquiv _ _ (εF.app P ≫ QB.map f) = QA.map (a.homEquiv _ _ f) ≫ ρF.app K)
    (hG : ∀ P K (f : G.obj P ⟶ K),
      bd.homEquiv _ _ (εG.app P ≫ QC.map f) = QB.map (b.homEquiv _ _ f) ≫ ρG.app K)
    (η : S ⋙ R ≅ U) (δ : SD ⋙ RD ≅ UD) (γ : F ⋙ G ⟶ H) (P : A)
    (hH : cd.homEquiv _ _ (εH.app P) = QA.map (c.unit.app P) ≫ ρH.app (H.obj P))
    (hγ : (a.comp b).homEquiv _ _ (γ.app P) =
      c.unit.app P ≫ η.inv.app (H.obj P))
    (hρ : ρF.app (S.obj (H.obj P)) ≫ RD.map (ρG.app (H.obj P)) ≫
      δ.hom.app (QC.obj (H.obj P)) = QA.map (η.hom.app (H.obj P)) ≫ ρH.app (H.obj P)) :
    (Adjunction.leftAdjointCompIso ad bd cd δ).hom.app (QA.obj P) ≫ εH.app P =
      GD.map (εF.app P) ≫ εG.app (F.obj P) ≫ QC.map (γ.app P) := by
  apply ((ad.comp bd).homEquiv _ _).injective
  rw [leftComp_transpose, hH]
  dsimp only [Functor.comp_obj]
  rw [normalizedAdjunction_composition a b ad bd εF εG ρF ρG hF hG
    P (H.obj P) (γ.app P), hγ]
  simp only [Category.assoc]
  rw [← Category.assoc] at hρ
  have hh := (Iso.eq_comp_inv (δ.app (QC.obj (H.obj P)))).mpr hρ
  rw [hh]
  exact map_iso_paste QA (c.unit.app P) (η.app (H.obj P))
    (ρH.app (H.obj P)) (δ.inv.app (QC.obj (H.obj P)))

end WeilConjectures
