/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedForgetTwoInjective.StandardBifunctorHomModel
import WeilConjectures.WeilSheaf.DerivedHomPrecomposition
import WeilConjectures.WeilSheaf.DerivedHom
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.Algebra.Homology.BifunctorHomCone
import WeilConjectures.Algebra.Homology.BifunctorHomComplex
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra

/-! # Native derived Hom with normalized product-total representatives

Source: Stacks Tags 0A95 and 08J7; native DerivedHom.lean and BifunctorHom.lean.
(blueprint: lem-sf-native-standard-hom-representatives)
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.RingedForgetTwoInjective
namespace NativeStandardAssembly
variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{v} C] [Abelian.HasKInjectiveResolutions C]
set_option quotPrecheck false
local notation "E" => (HomotopyCategory.KInjectives.Qh (C := C)).asEquivalence
local notation "q" => HomotopyCategory.quotient C (.up ℤ)
local notation "R" => (E).inverse ⋙ HomotopyCategory.KInjectives.ι

private instance rep_injective (K : DerivedCategory C) :
    CochainComplex.IsKInjective (((R).obj K).as) := by
  rw [CochainComplex.isKInjective_iff_rightOrthogonal]
  exact ((E).inverse.obj K).property

private noncomputable def eta (K : CochainComplex C ℤ) :
    (HomotopyCategory.quotient C (.up ℤ)).obj K ⟶ (R).obj (DerivedCategory.Q.obj K) :=
  (CochainComplex.IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient C (.up ℤ)).obj K)
    ((R).obj (DerivedCategory.Q.obj K)).as).surjective
    ((DerivedCategory.quotientCompQhIso C).hom.app K ≫
      (E).counitIso.inv.app (DerivedCategory.Q.obj K)) |>.choose

private lemma eta_spec (K : CochainComplex C ℤ) :
    DerivedCategory.Qh.map (eta K) =
      (DerivedCategory.quotientCompQhIso C).hom.app K ≫
        (E).counitIso.inv.app (DerivedCategory.Q.obj K) :=
  (CochainComplex.IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient C (.up ℤ)).obj K)
    ((R).obj (DerivedCategory.Q.obj K)).as).surjective _ |>.choose_spec

private lemma eta_naturality {K L : CochainComplex C ℤ} (a : K ⟶ L) :
    (HomotopyCategory.quotient C (.up ℤ)).map a ≫ eta L =
      eta K ≫ (R).map (DerivedCategory.Q.map a) := by
  apply (CochainComplex.IsKInjective.Qh_map_bijective _
    ((R).obj (DerivedCategory.Q.obj L)).as).injective
  simp only [Functor.map_comp, eta_spec, Category.assoc]
  rw [DerivedCategory.quotientCompQhIso_hom_naturality_assoc]
  exact congrArg ((DerivedCategory.quotientCompQhIso C).hom.app K ≫ ·)
    ((E).counitIso.inv.naturality (DerivedCategory.Q.map a))

private lemma eta_kinj (K : CochainComplex C ℤ) [K.IsKInjective] :
    eta K = (HomotopyCategory.KInjectives.ι.mapIso
      ((E).inverse.mapIso ((DerivedCategory.quotientCompQhIso C).app K).symm ≪≫
        ((E).unitIso.app (HomotopyCategory.KInjectives.mk K)).symm)).inv := by
  apply (CochainComplex.IsKInjective.Qh_map_bijective _
    ((R).obj (DerivedCategory.Q.obj K)).as).injective
  rw [eta_spec]
  simp only [Functor.mapIso_inv, Iso.trans_inv, Iso.symm_inv]
  change _ = (E).functor.map
    (((E).unitIso.app (HomotopyCategory.KInjectives.mk K)).hom ≫
      (E).inverse.map ((DerivedCategory.quotientCompQhIso C).hom.app K))
  rw [Functor.map_comp]
  exact ((E).counitIso.inv.naturality
    ((DerivedCategory.quotientCompQhIso C).hom.app K)).trans
      (congrArg (· ≫ (E).functor.map ((E).inverse.map
        ((DerivedCategory.quotientCompQhIso C).hom.app K)))
          ((E).counitInv_app_functor (HomotopyCategory.KInjectives.mk K)))
variable [HasCountableProducts C]
  (H : Cᵒᵖ ⥤ C ⥤ C) [H.Additive] [∀ M, (H.obj M).Additive]
private noncomputable def comparison (K I : CochainComplex C ℤ) :
    (DerivedCategory.bifunctorRHomOfComplex H I).obj (op (DerivedCategory.Q.obj K)) ⟶
      DerivedCategory.Q.obj (CochainComplex.bifunctorHomObj H K I) :=
  ((CochainComplex.bifunctorHomHomotopyFunctor H I).map (eta K)).unop ≫
    (DerivedCategory.quotientCompQhIso C).hom.app (CochainComplex.bifunctorHomObj H K I)

private lemma comparison_naturality {K L : CochainComplex C ℤ} (a : K ⟶ L)
    (I : CochainComplex C ℤ) :
    (DerivedCategory.bifunctorRHomOfComplex H I).map (DerivedCategory.Q.map a).op ≫
        comparison H K I =
      comparison H L I ≫ DerivedCategory.Q.map
        (CochainComplex.bifunctorHomMapLeft (H := H) (Y := I) a) := by
  let F := CochainComplex.bifunctorHomHomotopyFunctor H I
  have hh := congrArg (fun f ↦ (F.map f).unop) (eta_naturality a)
  simp only [Functor.map_comp, unop_comp] at hh
  change (F.map ((R).map (DerivedCategory.Q.map a))).unop ≫
    (F.map (eta K)).unop ≫ _ = _
  rw [← Category.assoc, ← hh, Category.assoc]
  rw [CochainComplex.bifunctorHomHomotopyFunctor_map]
  simpa only [comparison, Quiver.Hom.unop_op, Category.assoc] using
    congrArg ((F.map (eta L)).unop ≫ ·)
    (DerivedCategory.quotientCompQhIso_hom_naturality
      (CochainComplex.bifunctorHomMapLeft (H := H) (Y := I) a))

private lemma comparison_kinj (K I : CochainComplex C ℤ) [K.IsKInjective] :
    comparison H K I = (DerivedCategory.bifunctorRHomOfComplexObjIso H I K).hom := by
  simp only [comparison, eta_kinj, DerivedCategory.bifunctorRHomOfComplexObjIso,
    Iso.trans_hom, Iso.unop_hom, Iso.symm_hom, Functor.mapIso_inv]
  rfl

private lemma comparison_resolution (K I J : CochainComplex C ℤ) [J.IsKInjective]
    (α : K ⟶ J) [QuasiIso α] :
    comparison H K I =
      (DerivedCategory.bifunctorRHomOfComplex H I).map (inv (DerivedCategory.Q.map α)).op ≫
        (DerivedCategory.bifunctorRHomOfComplexObjIso H I J).hom ≫
          DerivedCategory.Q.map
            (CochainComplex.bifunctorHomMapLeft (H := H) (Y := I) α) := by
  rw [← comparison_kinj, ← comparison_naturality, ← Category.assoc,
    ← Functor.map_comp, ← op_comp, IsIso.hom_inv_id, op_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

private lemma comparison_right {I I' : CochainComplex C ℤ} (g : I ⟶ I')
    (K : CochainComplex C ℤ) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map
      (CochainComplex.bifunctorHomMapRight (H := H)
        (K := ((R).obj (DerivedCategory.Q.obj K)).as) g)) ≫ comparison H K I' =
      comparison H K I ≫ DerivedCategory.Q.map
        (CochainComplex.bifunctorHomMapRight (H := H) (K := K) g) := by
  have exchange {L L' : CochainComplex C ℤ} (a : L' ⟶ L) :
      CochainComplex.bifunctorHomMapRight (H := H) (K := L) g ≫
          CochainComplex.bifunctorHomMapLeft (H := H) (Y := I') a =
        CochainComplex.bifunctorHomMapLeft (H := H) (Y := I) a ≫
          CochainComplex.bifunctorHomMapRight (H := H) (K := L') g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply CochainComplex.bifunctorHomObj_hom_ext
    intro p r hpr
    simp only [HomologicalComplex.comp_f, Category.assoc,
      CochainComplex.bifunctorHomMapLeft_f_π,
      CochainComplex.bifunctorHomMapRight_f_π,
      CochainComplex.bifunctorHomMapLeft_f_π_assoc,
      CochainComplex.bifunctorHomMapRight_f_π_assoc, NatTrans.naturality]
  dsimp only [comparison]
  rw [← HomotopyCategory.quotient_map_out (eta K),
    CochainComplex.bifunctorHomHomotopyFunctor_map,
    CochainComplex.bifunctorHomHomotopyFunctor_map]
  simp only [Quiver.Hom.unop_op]
  rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, exchange,
    Functor.map_comp, Functor.map_comp, Category.assoc]
  simpa only [Category.assoc] using
    congrArg (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map
      (CochainComplex.bifunctorHomMapLeft (H := H) (Y := I) (eta K).out)) ≫ ·)
      (DerivedCategory.quotientCompQhIso_hom_naturality
        (CochainComplex.bifunctorHomMapRight (H := H) (K := K) g))

private lemma comparison_isIso (K I : CochainComplex C ℤ)
    (h : ∀ (J : CochainComplex C ℤ) [J.IsKInjective] (a : K ⟶ J) [QuasiIso a],
      IsIso (DerivedCategory.Q.map
        (CochainComplex.bifunctorHomMapLeft (H := H) (Y := I) a))) :
    IsIso (comparison H K I) := by
  obtain ⟨J, hJ, a, _, ha⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
  have := hJ
  have := ha
  have := h J a
  rw [comparison_resolution H K I J a]
  infer_instance

end NativeStandardAssembly

namespace NativeStandardAssembly

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{v} C] [Abelian.HasKInjectiveResolutions C]
  [HasCountableProducts C]
  (H : Cᵒᵖ ⥤ C ⥤ C) [H.Additive] [∀ M, (H.obj M).Additive]

set_option quotPrecheck false
local notation "q" => HomotopyCategory.quotient C (.up ℤ)
local notation "R" => (HomotopyCategory.KInjectives.Qh (C := C)).inv ⋙
  HomotopyCategory.KInjectives.ι

private noncomputable def rightHomotopy {I I' : CochainComplex C ℤ}
    {g g' : I ⟶ I'} (h : Homotopy g g') (K : CochainComplex C ℤ) :
    Homotopy (CochainComplex.bifunctorHomMapRight (H := H) (K := K) g)
      (CochainComplex.bifunctorHomMapRight g') where
  hom n m := CochainComplex.bifunctorHomLift H K I' m (fun p r _ ↦
    p.negOnePow • (CochainComplex.bifunctorHomπ H K I n p (p + n) rfl ≫
      (H.obj (op (K.X p))).map (h.hom (p + n) r)))
  zero n m hn := by
    apply CochainComplex.bifunctorHomObj_hom_ext
    intro p r hpr
    rw [CochainComplex.bifunctorHomLift_π]
    have hz : ¬ (ComplexShape.up ℤ).Rel r (p + n) := by
      simp only [ComplexShape.up_Rel] at hn ⊢
      omega
    rw [h.zero _ _ hz, Functor.map_zero, CategoryTheory.Limits.comp_zero, smul_zero,
      CategoryTheory.Limits.zero_comp]
  comm n := by
    classical
    apply CochainComplex.bifunctorHomObj_hom_ext
    intro p r hpr
    subst r
    simp only [CochainComplex.bifunctorHomMapRight_f_π,
      dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n by simp),
      Preadditive.add_comp, Category.assoc, CochainComplex.bifunctorHomLift_π,
      Linear.comp_units_smul]
    rw [CochainComplex.bifunctorHomObj_d_π_assoc H K I n (n + 1) p
      (p + (n + 1)) (by omega) (p + n) (p + 1) (by omega) (by omega)]
    rw [CochainComplex.bifunctorHomObj_d_π H K I' (n - 1) n p
      (p + n) rfl (p + (n - 1)) (p + 1) (by omega) (by omega)]
    simp only [Linear.comp_units_smul, Linear.units_smul_comp,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc,
      CochainComplex.bifunctorHomLift_π_assoc,
      smul_sub, smul_smul, Int.units_mul_self, one_smul, Int.negOnePow_succ]
    have hh := h.comm (p + n)
    rw [dNext_eq _
      (show (ComplexShape.up ℤ).Rel (p + n) (p + (n + 1)) by simp; omega),
      prevD_eq _
      (show (ComplexShape.up ℤ).Rel (p + (n - 1)) (p + n) by simp; omega)] at hh
    rw [hh, Functor.map_add, Functor.map_add, Functor.map_comp, Functor.map_comp,
      Preadditive.comp_add, Preadditive.comp_add]
    rw [NatTrans.naturality]
    have hc (t : ℤ) (ht : p + 1 + n = t) :
        CochainComplex.bifunctorHomπ H K I n (p + 1) t ht ≫
            (H.map (K.d p (p + 1)).op).app (I.X t) ≫
              (H.obj (op (K.X p))).map (h.hom t (p + n)) =
          CochainComplex.bifunctorHomπ H K I n (p + 1) (p + 1 + n) rfl ≫
            (H.map (K.d p (p + 1)).op).app (I.X (p + 1 + n)) ≫
              (H.obj (op (K.X p))).map (h.hom (p + 1 + n) (p + n)) := by
      subst t
      rfl
    rw [hc (p + (n + 1)) (by omega)]
    simp only [mul_neg, Int.units_mul_self, Units.smul_def,
      Units.val_neg, Units.val_one, neg_one_smul]
    abel

omit [HasDerivedCategory C] [Abelian.HasKInjectiveResolutions C] in
private lemma exchange {K K' I I' : CochainComplex C ℤ}
    (a : K' ⟶ K) (g : I ⟶ I') :
    CochainComplex.bifunctorHomMapRight (H := H) (K := K) g ≫
        CochainComplex.bifunctorHomMapLeft (H := H) (Y := I') a =
      CochainComplex.bifunctorHomMapLeft (H := H) (Y := I) a ≫
        CochainComplex.bifunctorHomMapRight (H := H) (K := K') g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply CochainComplex.bifunctorHomObj_hom_ext
  intro p r hpr
  simp only [HomologicalComplex.comp_f, Category.assoc,
    CochainComplex.bifunctorHomMapLeft_f_π,
    CochainComplex.bifunctorHomMapRight_f_π,
    CochainComplex.bifunctorHomMapLeft_f_π_assoc,
    CochainComplex.bifunctorHomMapRight_f_π_assoc, NatTrans.naturality]

private noncomputable def targetComplex : CochainComplex C ℤ ⥤
    ((DerivedCategory C)ᵒᵖ ⥤ DerivedCategory C) where
  obj I := DerivedCategory.bifunctorRHomOfComplex H I
  map {I I'} g := {
    app P := DerivedCategory.Qh.map ((q).map
      (CochainComplex.bifunctorHomMapRight (H := H) (K := ((R).obj P.unop).as) g))
    naturality P P' f := by
      change ((CochainComplex.bifunctorHomHomotopyFunctor H I).map
        ((R).map f.unop)).unop ≫ _ = _ ≫
          ((CochainComplex.bifunctorHomHomotopyFunctor H I').map
            ((R).map f.unop)).unop
      rw [← HomotopyCategory.quotient_map_out ((R).map f.unop),
        CochainComplex.bifunctorHomHomotopyFunctor_map,
        CochainComplex.bifunctorHomHomotopyFunctor_map]
      simp only [Quiver.Hom.unop_op]
      simpa only [Functor.map_comp] using
        congrArg (fun a ↦ DerivedCategory.Qh.map ((q).map a))
          (exchange H ((R).map f.unop).out g).symm }
  map_id I := by
    ext P
    change DerivedCategory.Qh.map ((q).map
      (CochainComplex.bifunctorHomMapRight (H := H) (K := ((R).obj P.unop).as)
        (𝟙 I))) = 𝟙 (DerivedCategory.Qh.obj ((q).obj
          (CochainComplex.bifunctorHomObj H ((R).obj P.unop).as I)))
    rw [CochainComplex.bifunctorHomMapRight_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  map_comp g g' := by
    ext P
    simp only [CochainComplex.bifunctorHomMapRight_comp, Functor.map_comp, NatTrans.comp_app]

private noncomputable def targetHomotopy : HomotopyCategory C (.up ℤ) ⥤
    ((DerivedCategory C)ᵒᵖ ⥤ DerivedCategory C) :=
  CategoryTheory.Quotient.lift _ (targetComplex H) (fun _ _ _ _ ⟨h⟩ ↦ by
    apply NatTrans.ext
    funext P
    exact congrArg DerivedCategory.Qh.map
      (HomotopyCategory.eq_of_homotopy _ _ (rightHomotopy H h _)))

private noncomputable def derivedBifunctor :
    (DerivedCategory C)ᵒᵖ × DerivedCategory C ⥤ DerivedCategory C :=
  CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj ((R) ⋙ targetHomotopy H)

end NativeStandardAssembly

namespace NativeStandardAssembly

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{v} C] [Abelian.HasKInjectiveResolutions C]
  [HasCountableProducts C]
  (H : Cᵒᵖ ⥤ C ⥤ C) [H.Additive] [∀ M, (H.obj M).Additive]
set_option quotPrecheck false
local notation "q" => HomotopyCategory.quotient C (.up ℤ)
local notation "E" => (HomotopyCategory.KInjectives.Qh (C := C)).asEquivalence
local notation "R" => (E).inverse ⋙ HomotopyCategory.KInjectives.ι

private noncomputable def epsilon (I : CochainComplex C ℤ) [I.IsKInjective] :
    (R).obj (DerivedCategory.Q.obj I) ≅ (q).obj I :=
  HomotopyCategory.KInjectives.ι.mapIso
    ((E).inverse.mapIso ((DerivedCategory.quotientCompQhIso C).app I).symm ≪≫
      ((E).unitIso.app (HomotopyCategory.KInjectives.mk I)).symm)

omit [HasCountableProducts C] in
private lemma epsilon_naturality {I I' : CochainComplex C ℤ}
    [I.IsKInjective] [I'.IsKInjective] (g : I ⟶ I') :
    (R).map (DerivedCategory.Q.map g) ≫ (epsilon I').hom =
      (epsilon I).hom ≫ (q).map g := by
  apply (cancel_epi (epsilon I).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  have hi : (epsilon I).inv = eta I := (eta_kinj I).symm
  have hi' : (epsilon I').inv = eta I' := (eta_kinj I').symm
  rw [← Category.assoc, hi, ← eta_naturality, Category.assoc, ← hi']
  simp

private noncomputable def sliceIso (L : DerivedCategory C) :
    Prod.sectL (DerivedCategory C)ᵒᵖ L ⋙ derivedBifunctor H ≅
      (targetHomotopy H).obj ((R).obj L) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    simp [derivedBifunctor, Functor.uncurry, Prod.sectL,
      CategoryTheory.Functor.map_id]
    rfl)

private noncomputable def beta (I : CochainComplex C ℤ) [I.IsKInjective]
    (P : (DerivedCategory C)ᵒᵖ) :
    (derivedBifunctor H).obj (P, DerivedCategory.Q.obj I) ≅
      (DerivedCategory.bifunctorRHomOfComplex H I).obj P :=
  ((targetHomotopy H).mapIso (epsilon I)).app P

private lemma beta_naturality {I I' : CochainComplex C ℤ}
    [I.IsKInjective] [I'.IsKInjective] (g : I ⟶ I')
    (P P' : (DerivedCategory C)ᵒᵖ) (f : P ⟶ P') :
    (derivedBifunctor H).map (X := (P, DerivedCategory.Q.obj I))
        (Y := (P', DerivedCategory.Q.obj I')) (f, DerivedCategory.Q.map g) ≫
        (beta H I' P').hom =
      (beta H I P).hom ≫ ((targetComplex H).map g).app P ≫
        (DerivedCategory.bifunctorRHomOfComplex H I').map f := by
  change (((targetHomotopy H).map ((R).map (DerivedCategory.Q.map g))).app P ≫
    ((targetHomotopy H).obj ((R).obj (DerivedCategory.Q.obj I'))).map f) ≫
      ((targetHomotopy H).map (epsilon I').hom).app P' =
    ((targetHomotopy H).map (epsilon I).hom).app P ≫
      ((targetHomotopy H).map ((q).map g)).app P ≫
        (DerivedCategory.bifunctorRHomOfComplex H I').map f
  rw [Category.assoc, NatTrans.naturality, ← Category.assoc,
    ← NatTrans.comp_app, ← Functor.map_comp, epsilon_naturality,
    Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rfl

private noncomputable def representativeIso
    (hinv : ∀ (K J I : CochainComplex C ℤ) [J.IsKInjective] [I.IsKInjective]
      (a : K ⟶ J) [QuasiIso a],
      IsIso (DerivedCategory.Q.map
        (CochainComplex.bifunctorHomMapLeft (H := H) (Y := I) a)))
    (K I : CochainComplex C ℤ) [I.IsKInjective] :
    (derivedBifunctor H).obj (op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (CochainComplex.bifunctorHomObj H K I) :=
  have := comparison_isIso H K I (fun J _ a _ ↦ hinv K J I a)
  beta H I (op (DerivedCategory.Q.obj K)) ≪≫ asIso (comparison H K I)

private lemma representative_naturality
    (hinv : ∀ (K J I : CochainComplex C ℤ) [J.IsKInjective] [I.IsKInjective]
      (a : K ⟶ J) [QuasiIso a],
      IsIso (DerivedCategory.Q.map
        (CochainComplex.bifunctorHomMapLeft (H := H) (Y := I) a)))
    (K K' I I' : CochainComplex C ℤ) [I.IsKInjective] [I'.IsKInjective]
    (f : K' ⟶ K) (g : I ⟶ I') :
    (derivedBifunctor H).map (X := (op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I))
        (Y := (op (DerivedCategory.Q.obj K'), DerivedCategory.Q.obj I'))
        ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map g) ≫
        (representativeIso H hinv K' I').hom =
      (representativeIso H hinv K I).hom ≫
        DerivedCategory.Q.map ((nativeHomComplex H).map
          (X := (op K, I)) (Y := (op K', I')) (f.op, g)) := by
  have hr : ((targetComplex H).map g).app (op (DerivedCategory.Q.obj K)) ≫
      comparison H K I' = comparison H K I ≫ DerivedCategory.Q.map
        (CochainComplex.bifunctorHomMapRight (H := H) (K := K) g) :=
    comparison_right H g K
  simp only [representativeIso, Iso.trans_hom, asIso_hom]
  rw [← Category.assoc, beta_naturality, Category.assoc, Category.assoc,
    comparison_naturality, ← Category.assoc _ _ (DerivedCategory.Q.map _), hr]
  simp only [nativeHomComplex, Category.assoc, ← DerivedCategory.Q.map_comp, exchange H]
  rfl

private noncomputable def representatives
    (hinv : ∀ (K J I : CochainComplex C ℤ) [J.IsKInjective] [I.IsKInjective]
      (a : K ⟶ J) [QuasiIso a],
      IsIso (DerivedCategory.Q.map
        (CochainComplex.bifunctorHomMapLeft (H := H) (Y := I) a))) :
    Representatives (nativeHomComplex H) (derivedBifunctor H) where
  iso := representativeIso H hinv
  naturality := representative_naturality H hinv
  inverts K K' I I' _ _ f g _ _ := by
    have hn := representative_naturality H hinv K K' I I' f g
    have : IsIso ((derivedBifunctor H).map
        (X := (op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I))
        (Y := (op (DerivedCategory.Q.obj K'), DerivedCategory.Q.obj I'))
        ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map g)) :=
      ((derivedBifunctor H).mapIso
        ((asIso (DerivedCategory.Q.map f)).op.prod
          (asIso (DerivedCategory.Q.map g)))).isIso_hom
    rw [← isIso_comp_left_iff (representativeIso H hinv K I).hom, ← hn]
    infer_instance

private noncomputable def normalizedSlice (L : DerivedCategory C) :
    Prod.sectL (DerivedCategory C)ᵒᵖ L ⋙ derivedBifunctor H ≅
      DerivedCategory.bifunctorRHom H L :=
  sliceIso H L ≪≫ (targetHomotopy H).mapIso
    ((R).mapIso (DerivedCategory.kInjectiveRepIso L) ≪≫
      epsilon (DerivedCategory.kInjectiveRep L))

private lemma normalizedSlice_eq
    (hinv : ∀ (K J I : CochainComplex C ℤ) [J.IsKInjective] [I.IsKInjective]
      (a : K ⟶ J) [QuasiIso a],
      IsIso (DerivedCategory.Q.map
        (CochainComplex.bifunctorHomMapLeft (H := H) (Y := I) a)))
    (L : DerivedCategory C) (K : CochainComplex C ℤ) [K.IsKInjective] :
    (normalizedSlice H L).hom.app (op (DerivedCategory.Q.obj K)) ≫
        (DerivedCategory.bifunctorRHomOfComplexObjIso H
          (DerivedCategory.kInjectiveRep L) K).hom =
      (derivedBifunctor H).map (X := (op (DerivedCategory.Q.obj K), L))
        (Y := (op (DerivedCategory.Q.obj K),
          DerivedCategory.Q.obj (DerivedCategory.kInjectiveRep L)))
        (𝟙 _, (DerivedCategory.kInjectiveRepIso L).hom) ≫
      ((representatives H hinv).iso K (DerivedCategory.kInjectiveRep L)).hom := by
  simp [normalizedSlice, representatives, representativeIso, beta, sliceIso,
    derivedBifunctor, Functor.uncurry, comparison_kinj,
    CategoryTheory.Functor.map_id]
  rfl

end NativeStandardAssembly

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
  [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- Native RHom has representatives for arbitrary sources and K-injective targets, and its
slice identification is normalized by the actual native K-injective source comparison.
The complex and its signed projections are the explicitly constructed standardHomModel;
only the universal derived extension and its normalized representative maps are asserted.
Source: Stacks 0A95, 08J7; BifunctorHom.lean, bifunctorRHomOfComplexObjIso.
(blueprint: lem-sf-native-standard-hom-representatives).
Proof: use the canonical functorial K-injective replacement in the second variable of the
native product-total Hom functor. It inverts source quasi-isomorphisms into a K-injective
target by quasiIso_bifunctorHomMapLeft. A target quasi-isomorphism between K-injectives is a
homotopy equivalence, and postcomposition carries its two homotopies to Hom-complex
homotopies, so it too is inverted after Q. Localize this bifunctor along Q^op × Q. Its
factorization isomorphism followed by the inverse of Hom(K, I → I_res) gives the asserted
representatives. Naturality of the augmentation proves both naturality squares; the same
invariance proves Representatives.inverts. These equations are the universal property that
determines the extension and the representative maps up to their unique compatible natural
isomorphism. For a fixed L, use its actual kInjectiveRep L. Naturality of the representatives
on K-injectives gives a natural isomorphism after the equivalence from the homotopy category
of K-injectives to D. Descend through that equivalence and compare with bifunctorRHomOfComplex.
On each K-injective K its component is exactly the displayed composite: the map induced by
kInjectiveRepIso L, then the representative isomorphism, then the inverse of the native source
comparison. This specifies the normalization and proves its naturality for all derived maps.
The rescaled projections change no underlying complex or chain map. -/
theorem nativeStandardHomRepresentatives
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] :
    ∃ H : (DerivedCategory (ProEtaleWeilSheaf k₀ l X))ᵒᵖ ×
        DerivedCategory (ProEtaleWeilSheaf k₀ l X) ⥤
          DerivedCategory (ProEtaleWeilSheaf k₀ l X),
      ∃ ρ : Representatives (standardHomModel (ihomBifunctor k₀ l X)).complex H,
        ∃ e : ∀ L : DerivedCategory (ProEtaleWeilSheaf k₀ l X),
          Prod.sectL (DerivedCategory (ProEtaleWeilSheaf k₀ l X))ᵒᵖ L ⋙ H ≅
            derivedHom k₀ l X L,
          ∀ (L : DerivedCategory (ProEtaleWeilSheaf k₀ l X))
            (K : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) [K.IsKInjective],
            (e L).hom.app (op (DerivedCategory.Q.obj K)) ≫
                (DerivedCategory.bifunctorRHomOfComplexObjIso (ihomBifunctor k₀ l X)
                  (DerivedCategory.kInjectiveRep L) K).hom =
              H.map (X := (op (DerivedCategory.Q.obj K), L))
                (Y := (op (DerivedCategory.Q.obj K),
                  DerivedCategory.Q.obj (DerivedCategory.kInjectiveRep L)))
                (𝟙 _, (DerivedCategory.kInjectiveRepIso L).hom) ≫
              (ρ.iso K (DerivedCategory.kInjectiveRep L)).hom  := by
  let H₀ := ihomBifunctor k₀ l X
  have hinv : ∀ (K J I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      [J.IsKInjective] [I.IsKInjective] (a : K ⟶ J) [QuasiIso a],
      IsIso (DerivedCategory.Q.map
        (CochainComplex.bifunctorHomMapLeft (H := H₀) (Y := I) a)) := by
    intro K J I _ _ a _
    have := quasiIso_bifunctorHomMapLeft (I := I) a
    infer_instance
  exact ⟨NativeStandardAssembly.derivedBifunctor H₀,
    NativeStandardAssembly.representatives H₀ hinv,
    NativeStandardAssembly.normalizedSlice H₀,
    NativeStandardAssembly.normalizedSlice_eq H₀ hinv⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
