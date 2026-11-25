/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.CategoryTheory.Adjunction.Parametrized
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.CategoryTheory.Localization.Opposite
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorRepresentatives

/-! # Normalized native currying on a prescribed total tensor model

Source: Stacks Tags 08J9, 0A90 and 0A97; the Hom portion of the ordinary
native closed construction (blueprint: lem-sf-native-ordinary-representative-currying).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

/- The degree-n sign below converts the native row convention to the usual Hom
   differential. In degree zero it disappears, giving the required counit formula. -/
namespace NativeCurrying
universe a b
open CochainComplex CochainComplex.HomComplex HomologicalComplex CategoryTheory.Category

variable {C : Type a} [Category.{b} C] [Abelian C]
  [HasCountableProducts C] [HasCountableCoproducts C]
  {T : C ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ C}
  [T.Additive] [∀ A, (T.obj A).Additive]
  [H.Additive] [∀ A, (H.obj A).Additive]
  (adj : T ⊣₂ H)

private instance totalExists (T : C ⥤ C ⥤ C)
    [T.Additive] [∀ A, (T.obj A).Additive] (P K : CochainComplex C ℤ) :
    HomologicalComplex.HasMapBifunctor P K T (.up ℤ) := by
  intro n
  let J := (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ)) ⁻¹' {n}
  have : HasColimitsOfShape (Discrete J) C :=
    HasCountableCoproducts.out J
  exact HasColimitsOfShape.has_colimit _

private noncomputable abbrev total (T : C ⥤ C ⥤ C)
    [T.Additive] [∀ A, (T.obj A).Additive] (P K : CochainComplex C ℤ) :=
  CochainComplex.mapBifunctor P K T

private noncomputable abbrev curry {P K Y : C} :
    ((T.obj P).obj K ⟶ Y) ≃+ (K ⟶ (H.obj (op P)).obj Y) :=
  (adj.adj P).homAddEquiv K Y

private noncomputable abbrev uncurry {P K Y : C} :=
  (curry adj (P := P) (K := K) (Y := Y)).symm

omit [HasCountableProducts C] [HasCountableCoproducts C] [T.Additive]
    [H.Additive] [∀ A, (H.obj A).Additive] in
private lemma curry_smul {P K Y : C} (r : ℤˣ) (f : (T.obj P).obj K ⟶ Y) :
    curry adj (r • f) = r • curry adj f :=
  by
  simpa only [Units.smul_def] using map_zsmul (curry adj) (r : ℤ) f

omit [HasCountableProducts C] [HasCountableCoproducts C] [T.Additive]
    [H.Additive] [∀ A, (H.obj A).Additive] in
private lemma uncurry_smul {P K Y : C} (r : ℤˣ)
    (f : K ⟶ (H.obj (op P)).obj Y) :
    uncurry adj (r • f) = r • uncurry adj f :=
  by
  simpa only [Units.smul_def] using map_zsmul (uncurry adj) (r : ℤ) f

omit [HasCountableProducts C] [HasCountableCoproducts C] [T.Additive]
    [H.Additive] [∀ A, (H.obj A).Additive] in
private lemma curry_one {P P' K Y : C} (f : P' ⟶ P)
    (g : (T.obj P).obj K ⟶ Y) :
    curry adj ((T.map f).app K ≫ g) = curry adj g ≫ (H.map f.op).app Y :=
  adj.homEquiv_naturality_one f g

omit [HasCountableProducts C] [HasCountableCoproducts C] [T.Additive]
    [H.Additive] [∀ A, (H.obj A).Additive] in
private lemma curry_two {P K K' Y : C} (f : K' ⟶ K)
    (g : (T.obj P).obj K ⟶ Y) :
    curry adj ((T.obj P).map f ≫ g) = f ≫ curry adj g :=
  adj.homEquiv_naturality_two f g

omit [HasCountableProducts C] [HasCountableCoproducts C] [T.Additive]
    [H.Additive] [∀ A, (H.obj A).Additive] in
private lemma curry_three {P K Y Y' : C} (g : (T.obj P).obj K ⟶ Y) (f : Y ⟶ Y') :
    curry adj (g ≫ f) = curry adj g ≫ (H.obj (op P)).map f :=
  adj.homEquiv_naturality_three f g

omit [HasCountableProducts C] in
private lemma total_d (T : C ⥤ C ⥤ C)
    [T.Additive] [∀ A, (T.obj A).Additive] (P K : CochainComplex C ℤ) (p q r r' : ℤ)
    (h : p + q = r) (h' : r + 1 = r') :
    ιMapBifunctor P K T (.up ℤ) p q r h ≫ (total T P K).d r r' =
      (T.map (P.d p (p + 1))).app (K.X q) ≫
          ιMapBifunctor P K T (.up ℤ) (p + 1) q r' (by change p + 1 + q = r'; omega) +
        p.negOnePow • ((T.obj (P.X p)).map (K.d q (q + 1)) ≫
          ιMapBifunctor P K T (.up ℤ) p (q + 1) r' (by change p + (q + 1) = r'; omega)) := by
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (rfl : (ComplexShape.up ℤ).Rel p (p + 1)) _ _
      (show p + 1 + q = r' by omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ (rfl : (ComplexShape.up ℤ).Rel q (q + 1)) _
      (show p + (q + 1) = r' by omega)]
  simp

omit [HasCountableProducts C] in
private lemma total_d_assoc (T : C ⥤ C ⥤ C)
    [T.Additive] [∀ A, (T.obj A).Additive] (P K : CochainComplex C ℤ) (p q r r' : ℤ)
    (h : p + q = r) (h' : r + 1 = r') {Z : C} (f : (total T P K).X r' ⟶ Z) :
    ιMapBifunctor P K T (.up ℤ) p q r h ≫ (total T P K).d r r' ≫ f =
      ((T.map (P.d p (p + 1))).app (K.X q) ≫
          ιMapBifunctor P K T (.up ℤ) (p + 1) q r' (by change p + 1 + q = r'; omega) +
        p.negOnePow • ((T.obj (P.X p)).map (K.d q (q + 1)) ≫
          ιMapBifunctor P K T (.up ℤ) p (q + 1) r' (by change p + (q + 1) = r'; omega))) ≫ f := by
  rw [← assoc, total_d T P K p q r r' h h']

variable {P Y K : CochainComplex C ℤ}

private noncomputable def curryCochain {n : ℤ} (z : Cochain (total T P K) Y n) :
    Cochain K (bifunctorHomObj H P Y) n :=
  Cochain.mk fun q _ _ ↦ Pi.lift fun t ↦ (t.p * n).negOnePow •
    curry adj (ιMapBifunctor P K T (.up ℤ) t.p q (t.p + q) rfl ≫
      z.v (t.p + q) t.q (by grind [t.hpq]))

private noncomputable def uncurryCochain {n : ℤ} (w : Cochain K (bifunctorHomObj H P Y) n) :
    Cochain (total T P K) Y n :=
  Cochain.mk fun r s hrs ↦ mapBifunctorDesc fun p q (hpq : p + q = r) ↦ (p * n).negOnePow •
    uncurry adj (w.v q (s - p) (by lia) ≫ bifunctorHomπ H P Y (s - p) p s (by lia))

@[reassoc]
private lemma curryCochain_v_π {n : ℤ} (z : Cochain (total T P K) Y n)
    (q q' : ℤ) (hqq' : q + n = q')
    (p s : ℤ) (hps : p + q' = s) (r : ℤ) (hr : p + q = r) (hrs : r + n = s) :
    (curryCochain adj z).v q q' hqq' ≫ bifunctorHomπ H P Y q' p s hps =
      (p * n).negOnePow • curry adj (ιMapBifunctor P K T (.up ℤ) p q r hr ≫ z.v r s hrs) := by
  subst hr
  exact Pi.lift_comp_π _ _

@[reassoc]
private lemma ι_uncurryCochain_v {n : ℤ} (w : Cochain K (bifunctorHomObj H P Y) n) (r s : ℤ)
    (hrs : r + n = s) (p q : ℤ) (hpq : p + q = r) (q' : ℤ) (hqq' : q + n = q')
    (hps : p + q' = s) :
    ιMapBifunctor P K T (.up ℤ) p q r hpq ≫ (uncurryCochain adj w).v r s hrs =
      (p * n).negOnePow • uncurry adj (w.v q q' hqq' ≫ bifunctorHomπ H P Y q' p s hps) := by
  obtain rfl : q' = s - p := by lia
  rw [uncurryCochain, Cochain.mk_v, ι_mapBifunctorDesc]

variable (P Y K) in
private noncomputable def cochainEquiv (n : ℤ) :
    Cochain (total T P K) Y n ≃+ Cochain K (bifunctorHomObj H P Y) n where
  toFun := curryCochain adj
  invFun := uncurryCochain adj
  left_inv z := by
    apply Cochain.ext
    intro r s hrs
    apply mapBifunctor.hom_ext
    intro p q hpq
    replace hpq : p + q = r := hpq
    rw [ι_uncurryCochain_v adj _ r s hrs p q hpq (q + n) rfl (by lia),
      curryCochain_v_π adj _ q (q + n) rfl p s (by lia) r hpq hrs,
      uncurry_smul adj, AddEquiv.symm_apply_apply (curry adj),
      smul_smul, Int.units_mul_self, one_smul]
  right_inv w := by
    ext q q' hqq' p s hps
    rw [curryCochain_v_π adj _ q q' hqq' p s hps (p + q) rfl (by lia),
      ι_uncurryCochain_v adj _ (p + q) s (by lia) p q rfl q' hqq' hps,
      curry_smul adj, AddEquiv.apply_symm_apply (curry adj),
      smul_smul, Int.units_mul_self, one_smul]
  map_add' z z' := by
    ext q q' hqq' p s hps
    rw [Cochain.add_v, Preadditive.add_comp,
      curryCochain_v_π adj _ q q' hqq' p s hps (p + q) rfl (by lia),
      curryCochain_v_π adj _ q q' hqq' p s hps (p + q) rfl (by lia),
      curryCochain_v_π adj _ q q' hqq' p s hps (p + q) rfl (by lia), Cochain.add_v,
      Preadditive.comp_add, map_add (curry adj), smul_add]

@[simp]
private lemma cochainEquiv_apply {n : ℤ} (z : Cochain (total T P K) Y n) :
    cochainEquiv adj P Y K n z = curryCochain adj z := rfl

@[simp]
private lemma cochainEquiv_symm_apply {n : ℤ} (w : Cochain K (bifunctorHomObj H P Y) n) :
    (cochainEquiv adj P Y K n).symm w = uncurryCochain adj w := rfl

@[simp]
private lemma curryCochain_uncurryCochain {n : ℤ} (w : Cochain K (bifunctorHomObj H P Y) n) :
    curryCochain adj (uncurryCochain adj w) = w :=
  (cochainEquiv adj P Y K n).apply_symm_apply w

@[simp]
private lemma uncurryCochain_curryCochain {n : ℤ} (z : Cochain (total T P K) Y n) :
    uncurryCochain adj (curryCochain adj z) = z :=
  (cochainEquiv adj P Y K n).symm_apply_apply z

private lemma curryCochain_δ (n m : ℤ) (z : Cochain (total T P K) Y n) :
    curryCochain adj (δ n m z) = δ n m (curryCochain adj z) := by
  by_cases hnm : n + 1 = m
  · subst hnm
    ext q q' hqq' p s hps
    rw [curryCochain_v_π adj _ q q' hqq' p s hps (p + q) rfl (by lia),
      δ_v n (n + 1) rfl z (p + q) s (by lia) (s - 1) (p + q + 1) (by lia) rfl,
      δ_v n (n + 1) rfl (curryCochain adj z) q q' hqq' (q' - 1) (q + 1) rfl rfl,
      Preadditive.add_comp, assoc, bifunctorHomObj_d_π H P Y (q' - 1) q' p s hps (s - 1) (p + 1)
        (by lia) (by lia), Linear.units_smul_comp, assoc,
      curryCochain_v_π adj _ (q + 1) q' (by lia) p s hps (p + q + 1) (by lia) (by lia),
      Linear.comp_units_smul, Preadditive.comp_sub, ← assoc, ← assoc,
      curryCochain_v_π adj _ q (q' - 1) (by lia) p (s - 1) (by lia) (p + q) rfl (by lia),
      curryCochain_v_π adj _ q (q' - 1) (by lia) (p + 1) s (by lia) (p + q + 1) (by lia) (by lia)]
    simp only [← curry_three adj, ← curry_one adj, ← curry_two adj, Preadditive.comp_add,
      Linear.comp_units_smul, assoc, total_d_assoc T P K p q (p + q) (p + q + 1) rfl rfl,
      Linear.units_smul_comp, ← curry_smul adj, ← map_sub (curry adj), ← map_add (curry adj)]
    congr 1
    simp only [Preadditive.add_comp, Linear.units_smul_comp, assoc, smul_add, smul_sub, smul_smul,
      mul_add, add_mul, mul_one, one_mul, Int.negOnePow_add, Int.negOnePow_one, mul_neg, neg_mul,
      Units.neg_smul, smul_neg, mul_comm _ p.negOnePow, mul_left_comm _ p.negOnePow, ← mul_assoc,
      Int.units_mul_self, mul_comm n.negOnePow]
    abel
  · rw [δ_shape _ _ hnm, δ_shape _ _ hnm]
    exact (cochainEquiv adj P Y K m).map_zero

private lemma uncurryCochain_δ (n m : ℤ) (w : Cochain K (bifunctorHomObj H P Y) n) :
    uncurryCochain adj (δ n m w) = δ n m (uncurryCochain adj w) :=
  (cochainEquiv adj P Y K m).injective (by
    rw [cochainEquiv_apply, cochainEquiv_apply, curryCochain_δ adj, curryCochain_uncurryCochain adj,
      curryCochain_uncurryCochain adj])

variable (P Y K) in
private noncomputable def internalHomEquiv : (total T P K ⟶ Y) ≃ (K ⟶ bifunctorHomObj H P Y) where
  toFun f := Cocycle.homOf (Cocycle.mk (curryCochain adj (Cochain.ofHom f)) 1 (zero_add 1) (by
    rw [← curryCochain_δ adj, δ_ofHom, ← cochainEquiv_apply, map_zero]))
  invFun g := Cocycle.homOf (Cocycle.mk (uncurryCochain adj (Cochain.ofHom g)) 1 (zero_add 1) (by
    rw [← uncurryCochain_δ adj, δ_ofHom, ← cochainEquiv_symm_apply, map_zero]))
  left_inv f := Cochain.ofHom_injective (by
    rw [Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.mk_coe, Cocycle.cochain_ofHom_homOf_eq_coe,
      Cocycle.mk_coe, uncurryCochain_curryCochain adj])
  right_inv g := Cochain.ofHom_injective (by
    rw [Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.mk_coe, Cocycle.cochain_ofHom_homOf_eq_coe,
      Cocycle.mk_coe, curryCochain_uncurryCochain adj])

@[simp]
private lemma ofHom_internalHomEquiv (f : total T P K ⟶ Y) :
    Cochain.ofHom (internalHomEquiv adj P Y K f) = curryCochain adj (Cochain.ofHom f) := by
  simp [internalHomEquiv]

@[simp]
private lemma ofHom_internalHomEquiv_symm (g : K ⟶ bifunctorHomObj H P Y) :
    Cochain.ofHom ((internalHomEquiv adj P Y K).symm g) = uncurryCochain adj (Cochain.ofHom g) := by
  simp [internalHomEquiv]

@[reassoc]
private lemma internalHomEquiv_f_π (g : total T P K ⟶ Y) (q p s : ℤ) (hps : p + q = s) :
    (internalHomEquiv adj P Y K g).f q ≫ bifunctorHomπ H P Y q p s hps =
      curry adj (HomologicalComplex.ιMapBifunctor P K T (.up ℤ) p q s hps ≫ g.f s) := by
  rw [← Cochain.ofHom_v, ofHom_internalHomEquiv adj,
    curryCochain_v_π adj _ q q (add_zero q) p s hps s hps (add_zero s), Cochain.ofHom_v, mul_zero,
    Int.negOnePow_zero, one_smul]

private noncomputable def curryHomotopy {f f' : total T P K ⟶ Y} (h : Homotopy f f') :
    Homotopy (internalHomEquiv adj P Y K f) (internalHomEquiv adj P Y K f') :=
  (Cochain.equivHomotopy _ _).symm ⟨curryCochain adj (Cochain.ofHomotopy h), by
    rw [ofHom_internalHomEquiv adj, ofHom_internalHomEquiv adj,
      ← curryCochain_δ adj, δ_ofHomotopy,
      ← cochainEquiv_apply, ← cochainEquiv_apply, ← cochainEquiv_apply,
      ← map_add, sub_add_cancel]⟩

private noncomputable def uncurryHomotopy {g g' : K ⟶ bifunctorHomObj H P Y}
    (h : Homotopy g g') :
    Homotopy ((internalHomEquiv adj P Y K).symm g)
      ((internalHomEquiv adj P Y K).symm g') :=
  (Cochain.equivHomotopy _ _).symm ⟨uncurryCochain adj (Cochain.ofHomotopy h), by
    rw [ofHom_internalHomEquiv_symm adj, ofHom_internalHomEquiv_symm adj,
      ← uncurryCochain_δ adj, δ_ofHomotopy,
      ← cochainEquiv_symm_apply, ← cochainEquiv_symm_apply, ← cochainEquiv_symm_apply,
      ← map_add, sub_add_cancel]⟩

private noncomputable def homotopyEquiv :
    ((HomotopyCategory.quotient C (.up ℤ)).obj (total T P K) ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj Y) ≃
    ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj (bifunctorHomObj H P Y)) where
  toFun := Quot.lift
    (fun f ↦ (HomotopyCategory.quotient C (.up ℤ)).map (internalHomEquiv adj P Y K f))
    (by
      intro f f' h
      obtain ⟨h⟩ := (HomRel.compClosure_iff_self _ _ _).1 h
      exact HomotopyCategory.eq_of_homotopy _ _ (curryHomotopy adj h))
  invFun := Quot.lift
    (fun g ↦ (HomotopyCategory.quotient C (.up ℤ)).map
      ((internalHomEquiv adj P Y K).symm g))
    (by
      intro g g' h
      obtain ⟨h⟩ := (HomRel.compClosure_iff_self _ _ _).1 h
      exact HomotopyCategory.eq_of_homotopy _ _ (uncurryHomotopy adj h))
  left_inv := by
    intro f
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective f
    change (HomotopyCategory.quotient C (.up ℤ)).map
      ((internalHomEquiv adj P Y K).symm (internalHomEquiv adj P Y K f)) = _
    rw [Equiv.symm_apply_apply]
  right_inv := by
    intro g
    obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective g
    change (HomotopyCategory.quotient C (.up ℤ)).map
      (internalHomEquiv adj P Y K ((internalHomEquiv adj P Y K).symm g)) = _
    rw [Equiv.apply_symm_apply]

private theorem internalHomEquiv_naturality
    {P' K' Y' : CochainComplex C ℤ} (f : P' ⟶ P) (g : K' ⟶ K) (h : Y ⟶ Y')
    (a : total T P K ⟶ Y) :
    internalHomEquiv adj P' Y' K' (mapBifunctorMap f g T (.up ℤ) ≫ a ≫ h) =
      g ≫ internalHomEquiv adj P Y K a ≫
        (bifunctorHomMapLeft (H := H) (Y := Y) f ≫
          bifunctorHomMapRight (H := H) (K := P') h) := by
  ext q p s hps
  simp only [HomologicalComplex.comp_f, assoc, internalHomEquiv_f_π adj,
    bifunctorHomMapRight_f_π, bifunctorHomMapLeft_f_π_assoc,
    ι_mapBifunctorMap_assoc]
  rw [internalHomEquiv_f_π_assoc adj]
  simp only [← assoc]
  rw [curry_three adj]
  simp only [assoc, curry_one adj, curry_two adj]

include adj in
private theorem hom_isKInjective (P Y : CochainComplex C ℤ) [Y.IsKInjective]
    (hP : ∀ K : CochainComplex C ℤ, K.Acyclic → (total T P K).Acyclic) :
    (bifunctorHomObj H P Y).IsKInjective := by
  constructor
  intro K f hK
  let a := (internalHomEquiv adj P Y K).symm f
  let h := IsKInjective.homotopyZero a (hP K hK)
  have hz : internalHomEquiv adj P Y K (0 : total T P K ⟶ Y) = 0 := by
    apply Cochain.ofHom_injective
    rw [ofHom_internalHomEquiv adj, Cochain.ofHom_zero, Cochain.ofHom_zero]
    change cochainEquiv adj P Y K 0 0 = 0
    exact map_zero _
  simpa only [a, Equiv.apply_symm_apply, hz] using
    (show Nonempty (Homotopy (internalHomEquiv adj P Y K a)
      (internalHomEquiv adj P Y K (0 : total T P K ⟶ Y))) from
        ⟨curryHomotopy adj h⟩)

private noncomputable def qHomEquiv [HasDerivedCategory.{b} C]
    (K Y : CochainComplex C ℤ) [Y.IsKInjective] :
    ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj Y) ≃
      (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj Y) :=
  (Equiv.ofBijective _ (IsKInjective.Qh_map_bijective _ Y)).trans
    (Iso.homCongr ((DerivedCategory.quotientCompQhIso C).app K)
      ((DerivedCategory.quotientCompQhIso C).app Y))

omit [HasCountableProducts C] [HasCountableCoproducts C] in
private theorem qHomEquiv_map [HasDerivedCategory.{b} C]
    (K Y : CochainComplex C ℤ) [Y.IsKInjective] (f : K ⟶ Y) :
    qHomEquiv K Y ((HomotopyCategory.quotient C (.up ℤ)).map f) =
      DerivedCategory.Q.map f := by
  change (DerivedCategory.quotientCompQhIso C).inv.app K ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f) ≫
      (DerivedCategory.quotientCompQhIso C).hom.app Y = _
  rw [DerivedCategory.quotientCompQhIso_hom_naturality, Iso.inv_hom_id_app_assoc]

private noncomputable def derivedEquiv [HasDerivedCategory.{b} C]
    (HD : (DerivedCategory C)ᵒᵖ × DerivedCategory C ⥤ DerivedCategory C)
    (R : NativeHomRepresentatives H HD) (P K Y : CochainComplex C ℤ) [Y.IsKInjective]
    (hP : ∀ L : CochainComplex C ℤ, L.Acyclic → (total T P L).Acyclic) :
    (DerivedCategory.Q.obj (total T P K) ⟶ DerivedCategory.Q.obj Y) ≃
      (DerivedCategory.Q.obj K ⟶
        HD.obj (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj Y)) := by
  let := hom_isKInjective adj P Y hP
  exact (qHomEquiv (total T P K) Y).symm.trans
    ((homotopyEquiv adj).trans
      ((qHomEquiv K (bifunctorHomObj H P Y)).trans
        (R.model P Y inferInstance).symm.homToEquiv))

private theorem derivedEquiv_map [HasDerivedCategory.{b} C]
    (HD : (DerivedCategory C)ᵒᵖ × DerivedCategory C ⥤ DerivedCategory C)
    (R : NativeHomRepresentatives H HD) (P K Y : CochainComplex C ℤ) [Y.IsKInjective]
    (hP : ∀ L : CochainComplex C ℤ, L.Acyclic → (total T P L).Acyclic)
    (f : total T P K ⟶ Y) :
    derivedEquiv adj HD R P K Y hP (DerivedCategory.Q.map f) =
      DerivedCategory.Q.map (internalHomEquiv adj P Y K f) ≫
        (R.model P Y inferInstance).inv := by
  let := hom_isKInjective adj P Y hP
  change (qHomEquiv K (bifunctorHomObj H P Y))
      (homotopyEquiv adj ((qHomEquiv (total T P K) Y).symm
        (DerivedCategory.Q.map f))) ≫ _ = _
  rw [← qHomEquiv_map, Equiv.symm_apply_apply]
  change qHomEquiv K (bifunctorHomObj H P Y)
    ((HomotopyCategory.quotient C (.up ℤ)).map _) ≫ _ = _
  rw [qHomEquiv_map]
  rfl

private theorem derivedEquiv_naturality [HasDerivedCategory.{b} C]
    (HD : (DerivedCategory C)ᵒᵖ × DerivedCategory C ⥤ DerivedCategory C)
    (R : NativeHomRepresentatives H HD)
    (P P' K K' Y Y' : CochainComplex C ℤ) [Y.IsKInjective] [Y'.IsKInjective]
    (hP : ∀ L : CochainComplex C ℤ, L.Acyclic → (total T P L).Acyclic)
    (hP' : ∀ L : CochainComplex C ℤ, L.Acyclic → (total T P' L).Acyclic)
    (f : P' ⟶ P) (g : K' ⟶ K) (h : Y ⟶ Y')
    (a : DerivedCategory.Q.obj (total T P K) ⟶ DerivedCategory.Q.obj Y) :
    derivedEquiv adj HD R P' K' Y' hP'
        (DerivedCategory.Q.map (mapBifunctorMap f g T (.up ℤ)) ≫
          a ≫ DerivedCategory.Q.map h) =
      DerivedCategory.Q.map g ≫ derivedEquiv adj HD R P K Y hP a ≫
        HD.map (Prod.mkHom (DerivedCategory.Q.map f).op (DerivedCategory.Q.map h)) := by
  let q := HomotopyCategory.quotient C (.up ℤ)
  obtain ⟨a, rfl⟩ := (qHomEquiv (total T P K) Y).surjective a
  obtain ⟨a, rfl⟩ := q.map_surjective a
  rw [qHomEquiv_map]
  simp only [← CategoryTheory.Functor.map_comp]
  rw [derivedEquiv_map, derivedEquiv_map, internalHomEquiv_naturality adj f g h]
  simp only [CategoryTheory.Functor.map_comp, assoc]
  have hr := R.naturality P' P Y Y' inferInstance inferInstance f h
  have hr' : DerivedCategory.Q.map
      (bifunctorHomMapLeft (H := H) (Y := Y) f ≫
        bifunctorHomMapRight (H := H) (K := P') h) ≫ (R.model P' Y' inferInstance).inv =
      (R.model P Y inferInstance).inv ≫
        HD.map (Prod.mkHom (DerivedCategory.Q.map f).op (DerivedCategory.Q.map h)) := by
    apply (cancel_mono (R.model P' Y' inferInstance).hom).1
    simp only [assoc, Iso.inv_hom_id, comp_id]
    rw [hr, Iso.inv_hom_id_assoc]
  simpa only [CategoryTheory.Functor.map_comp, assoc] using
    congrArg (fun z ↦ DerivedCategory.Q.map g ≫
      DerivedCategory.Q.map (internalHomEquiv adj P Y K a) ≫ z) hr'

private theorem derivedEquiv_symm_map [HasDerivedCategory.{b} C]
    (HD : (DerivedCategory C)ᵒᵖ × DerivedCategory C ⥤ DerivedCategory C)
    (R : NativeHomRepresentatives H HD) (P K Y : CochainComplex C ℤ) [Y.IsKInjective]
    (hP : ∀ L : CochainComplex C ℤ, L.Acyclic → (total T P L).Acyclic)
    (φ : K ⟶ bifunctorHomObj H P Y) :
    (derivedEquiv adj HD R P K Y hP).symm
        (DerivedCategory.Q.map φ ≫ (R.model P Y inferInstance).inv) =
      DerivedCategory.Q.map ((internalHomEquiv adj P Y K).symm φ) := by
  apply (derivedEquiv adj HD R P K Y hP).injective
  rw [Equiv.apply_symm_apply, derivedEquiv_map, Equiv.apply_symm_apply]

private theorem uncurry_component (P K Y : CochainComplex C ℤ)
    (φ : K ⟶ bifunctorHomObj H P Y) (p q n : ℤ) (hpq : p + q = n) :
    ιMapBifunctor P K T (.up ℤ) p q n hpq ≫
        ((internalHomEquiv adj P Y K).symm φ).f n =
      (T.obj (P.X p)).map (φ.f q ≫ bifunctorHomπ H P Y q p n hpq) ≫
        (adj.adj (P.X p)).counit.app (Y.X n) := by
  have h := internalHomEquiv_f_π adj ((internalHomEquiv adj P Y K).symm φ) q p n hpq
  rw [Equiv.apply_symm_apply] at h
  rw [h]
  change _ = (T.obj (P.X p)).map
    ((adj.adj (P.X p)).homEquiv _ _ _) ≫ _
  rw [← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]

end NativeCurrying

attribute [local irreducible] NativeCurrying.cochainEquiv NativeCurrying.internalHomEquiv
  NativeCurrying.homotopyEquiv NativeCurrying.qHomEquiv NativeCurrying.derivedEquiv

/- Descend inverse currying as a natural isomorphism of the two Hom functors. -/
namespace CurryingDescent
universe a b
variable {D : Type a} [Category.{b} D] [MonoidalCategory D]

private noncomputable def tensorHoms :
    (D)ᵒᵖ ×
      ((D)ᵒᵖ × D) ⥤
        Type b where
  obj X := (X.1.unop ⊗ X.2.1.unop ⟶ X.2.2)
  map f := ↾fun ψ ↦ (f.1.unop ⊗ₘ f.2.1.unop) ≫ ψ ≫ f.2.2
  map_id X := by
    ext ψ
    simp
  map_comp f g := by
    ext ψ
    change ((g.1.unop ≫ f.1.unop) ⊗ₘ (g.2.1.unop ≫ f.2.1.unop)) ≫ ψ ≫
      (f.2.2 ≫ g.2.2) =
        (g.1.unop ⊗ₘ g.2.1.unop) ≫
          ((f.1.unop ⊗ₘ f.2.1.unop) ≫ ψ ≫ f.2.2) ≫ g.2.2
    rw [← tensorHom_comp_tensorHom]
    simp only [Category.assoc]

variable (H : Dᵒᵖ × D ⥤ D)

private noncomputable def homHoms :
    (D)ᵒᵖ ×
      ((D)ᵒᵖ × D) ⥤
        Type b where
  obj X := (X.1.unop ⟶ (H).obj
    (X.2.1, X.2.2))
  map f := ↾fun φ ↦ f.1.unop ≫ φ ≫
    (H).map (f.2.1, f.2.2)
  map_id X := by
    ext φ
    change (𝟙 _ ≫ φ ≫ (H).map (𝟙 _)) = φ
    erw [CategoryTheory.Functor.map_id]
    simp only [Category.id_comp, Category.comp_id]
  map_comp f g := by
    ext φ
    change (g.1.unop ≫ f.1.unop) ≫ φ ≫
      (H).map
        ((f.2.1, f.2.2) ≫ (g.2.1, g.2.2)) =
      g.1.unop ≫ (f.1.unop ≫ φ ≫
        (H).map (f.2.1, f.2.2)) ≫
          (H).map (g.2.1, g.2.2)
    rw [CategoryTheory.Functor.map_comp]
    simp only [Category.assoc]

private noncomputable def derivedEquiv (e : homHoms H ≅ tensorHoms (D := D))
    (P L M : D) :
    (P ⊗ L ⟶ M) ≃ (P ⟶ (H).obj (op L, M)) :=
  (e.app (op P, (op L, M))).toEquiv.symm

private theorem derivedEquiv_symm_naturality (e : homHoms H ≅ tensorHoms (D := D))
    (P P' L L' M M' : D)
    (f : P' ⟶ P) (g : L' ⟶ L) (h : M ⟶ M')
    (φ : P ⟶ (H).obj (op L, M)) :
    (derivedEquiv H e P' L' M').symm
        (f ≫ φ ≫ (H).map (g.op, h)) =
      (f ⊗ₘ g) ≫ (derivedEquiv H e P L M).symm φ ≫ h := by
  exact congrArg (fun k ↦ k φ)
    (e.hom.naturality
      (X := (op P, (op L, M))) (Y := (op P', (op L', M')))
        (Prod.mkHom f.op (Prod.mkHom g.op h)))

end CurryingDescent

namespace OrdinaryCurrying
universe a b
variable {C : Type a} [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{b} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [Abelian.HasFunctorialFlatResolution C] {B : C} [MonObj B] [IsCommMonObj B]
  [HasDerivedCategory.{b} (Mod C B)]

local instance : HasLimitsOfSize.{b, b} C := inferInstance
local instance : HasColimitsOfSize.{b, b} C := inferInstance
local instance : HasLimitsOfSize.{b, b} (Mod C B) := inferInstance
local instance : HasColimitsOfSize.{b, b} (Mod C B) := inferInstance

open GenericOrdinaryTensor

private instance tensorRightColimits (X : Mod C B) :
    PreservesColimitsOfShape ℤ ((curriedTensor (Mod C B)).flip.obj X) :=
  preservesColimitsOfShape_of_natIso (F := tensorLeft X)
    (NatIso.ofComponents (fun Z ↦ β_ X Z) (by intros; simp [curriedTensor]))

private instance gradedTensor (X Y : GradedObject ℤ (Mod C B)) : X.HasTensor Y :=
  inferInstance

private instance gradedTensorFour (W X Y Z : GradedObject ℤ (Mod C B)) :
    GradedObject.HasTensor₄ObjExt W X Y Z := inferInstance

private instance gradedTensorLeft (X Y Z : GradedObject ℤ (Mod C B)) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z := inferInstance

private instance gradedTensorRight (X Y Z : GradedObject ℤ (Mod C B)) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z := inferInstance

private noncomputable abbrev ordinaryBifunctor : Mod C B ⥤ Mod C B ⥤ Mod C B :=
  GenericOrdinaryTensor.ordinaryBifunctor

private noncomputable abbrev ordinaryH : (Mod C B)ᵒᵖ ⥤ Mod C B ⥤ Mod C B := PrecompositionAux.H

private noncomputable abbrev ordinaryTotal (P Q : CochainComplex (Mod C B) ℤ) :=
  GenericOrdinaryTensor.ordinaryTotal P Q

private abbrev ordinaryFlat (P : CochainComplex (Mod C B) ℤ) : Prop :=
  GenericOrdinaryTensor.ordinaryFlat P

private abbrev flatProperty : ObjectProperty (CochainComplex (Mod C B) ℤ) := ordinaryFlat

private noncomputable def adj :
    (ordinaryBifunctor (C := C) (B := B)) ⊣₂ ordinaryH where
  adj P := Mod.ihomAdjunction P
  unit_whiskerRight_map {P P'} f := by
    apply NatTrans.ext
    funext Q
    exact (unit_conjugateEquiv (Mod.ihomAdjunction P') (Mod.ihomAdjunction P)
      (Mod.tensorLeftMap f) Q).symm

-- Functorial flat resolutions land in the native acyclic-test flat subcategory.
private theorem flatLocalization :
    (ObjectProperty.ι (flatProperty (C := C) (B := B)) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso (Mod C B) (.up ℤ)).inverseImage
        (ObjectProperty.ι (flatProperty (C := C) (B := B)))) := by
  let W := HomologicalComplex.quasiIso (Mod C B) (.up ℤ)
  let P : ObjectProperty (CochainComplex (Mod C B) ℤ) := ordinaryFlat
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution (Mod C B)).some.reduced
  have flat (K : CochainComplex (Mod C B) ℤ) (hK : W.kFlat K) : P K := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic] at hK
    intro Z hZ n
    have hz := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (Z ⊗ K)).mp
        (hK _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic Z).mpr hZ)).2
    exact (hz n).of_iso (ordinaryTotalIso K Z).symm
  let ρ := ObjectProperty.lift P Λ.resolutionFunctor
    (fun K ↦ flat _ (Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K))
  let Φ : LocalizerMorphism (W.inverseImage P.ι) W :=
    { functor := P.ι
      map := fun _ _ _ h ↦ h }
  have : Φ.IsInduced := ⟨rfl⟩
  have : Φ.IsLocalizedEquivalence :=
    Φ.isLocalizedEquivalence_of_functorial_left_resolutions (ρ := ρ) Λ.resolutionNatTrans
      (fun K ↦ by
        dsimp only [W]
        rw [HomologicalComplex.mem_quasiIso_iff]
        infer_instance) rfl
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization Φ DerivedCategory.Q

attribute [local instance] flatLocalization

private noncomputable def representativeFunctor :=
  (DerivedCategory.Q (C := Mod C B)).op.prod
    (((ObjectProperty.ι (flatProperty (C := C) (B := B))) ⋙
      DerivedCategory.Q).op.prod (CochainComplex.KInjectives.ι (C := Mod C B) ⋙ DerivedCategory.Q))

private def representativeW :=
  let W := HomologicalComplex.quasiIso (Mod C B) (.up ℤ)
  W.op.prod ((W.inverseImage
    (ObjectProperty.ι (flatProperty (C := C) (B := B)))).op.prod
      (CochainComplex.KInjectives.quasiIso (Mod C B)))

private instance representativeLocalization :
    (representativeFunctor (C := C) (B := B)).IsLocalization representativeW := by
  let : Abelian.HasKInjectiveResolutions (Mod C B) :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{b}
  let W := HomologicalComplex.quasiIso (Mod C B) (.up ℤ)
  have : (DerivedCategory.Q (C := Mod C B)).IsLocalization W := inferInstance
  have : (ObjectProperty.ι (flatProperty (C := C) (B := B)) ⋙
      DerivedCategory.Q).IsLocalization
        (W.inverseImage (ObjectProperty.ι (flatProperty (C := C) (B := B)))) :=
    flatLocalization
  have : (CochainComplex.KInjectives.ι (C := Mod C B) ⋙
      DerivedCategory.Q).IsLocalization (CochainComplex.KInjectives.quasiIso (Mod C B)) :=
    inferInstance
  -- The restricted property is a definition, so register its identity instance explicitly.
  have : (CochainComplex.KInjectives.quasiIso (Mod C B)).ContainsIdentities := by
    dsimp only [CochainComplex.KInjectives.quasiIso]
    infer_instance
  dsimp only [representativeFunctor, representativeW]
  infer_instance

variable
    (H : (DerivedCategory (Mod C B))ᵒᵖ × DerivedCategory (Mod C B) ⥤
      DerivedCategory (Mod C B))

private noncomputable def representativeEquiv
    (R : NativeHomRepresentatives ordinaryH H)
    (model : ∀ P Q : CochainComplex (Mod C B) ℤ, ordinaryFlat P →
      (DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj P ≅
        DerivedCategory.Q.obj (ordinaryTotal P Q)))
    (P Q I : CochainComplex (Mod C B) ℤ) (hP : ordinaryFlat P) [I.IsKInjective] :
    (DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj I) ≃
      (DerivedCategory.Q.obj Q ⟶ H.obj (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I)) :=
  (model P Q hP).homFromEquiv.trans
    (NativeCurrying.derivedEquiv adj H R P Q I hP)

private theorem representativeEquiv_uncurry
    (R : NativeHomRepresentatives ordinaryH H)
    (model : ∀ P Q : CochainComplex (Mod C B) ℤ, ordinaryFlat P →
      (DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj P ≅
        DerivedCategory.Q.obj (ordinaryTotal P Q)))
    (P Q I : CochainComplex (Mod C B) ℤ) (hP : ordinaryFlat P) [I.IsKInjective]
    (φ : Q ⟶ CochainComplex.bifunctorHomObj ordinaryH P I) :
    (representativeEquiv H R model P Q I hP).symm
        (DerivedCategory.Q.map φ ≫ (R.model P I inferInstance).inv) =
      (model P Q hP).hom ≫ DerivedCategory.Q.map
        ((NativeCurrying.internalHomEquiv adj P I Q).symm φ) := by
  change (model P Q hP).hom ≫
    (NativeCurrying.derivedEquiv adj H R P Q I hP).symm _ = _
  rw [NativeCurrying.derivedEquiv_symm_map]

private theorem representativeEquiv_naturality
    (R : NativeHomRepresentatives ordinaryH H)
    (model : ∀ P Q : CochainComplex (Mod C B) ℤ, ordinaryFlat P →
      (DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj P ≅
        DerivedCategory.Q.obj (ordinaryTotal P Q)))
    (hn : ∀ (P Q P' Q' : CochainComplex (Mod C B) ℤ)
      (hP : ordinaryFlat P) (hP' : ordinaryFlat P') (f : P ⟶ P') (g : Q ⟶ Q'),
      (DerivedCategory.Q.map g ⊗ₘ DerivedCategory.Q.map f) ≫ (model P' Q' hP').hom =
        (model P Q hP).hom ≫ DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g ordinaryBifunctor (.up ℤ)))
    (P P' Q Q' I I' : CochainComplex (Mod C B) ℤ)
    (hP : ordinaryFlat P) (hP' : ordinaryFlat P') [I.IsKInjective] [I'.IsKInjective]
    (f : Q' ⟶ Q) (g : P' ⟶ P) (h : I ⟶ I')
    (φ : DerivedCategory.Q.obj Q ⟶
      H.obj (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I)) :
    (representativeEquiv H R model P' Q' I' hP').symm
        (DerivedCategory.Q.map f ≫ φ ≫ H.map
          (Prod.mkHom (DerivedCategory.Q.map g).op (DerivedCategory.Q.map h))) =
      (DerivedCategory.Q.map f ⊗ₘ DerivedCategory.Q.map g) ≫
        (representativeEquiv H R model P Q I hP).symm φ ≫ DerivedCategory.Q.map h := by
  have hd := NativeCurrying.derivedEquiv_naturality adj H R P P' Q Q' I I'
    hP hP' g f h ((NativeCurrying.derivedEquiv adj H R P Q I hP).symm φ)
  rw [Equiv.apply_symm_apply] at hd
  have he := congrArg (NativeCurrying.derivedEquiv adj H R P' Q' I' hP').symm hd
  rw [Equiv.symm_apply_apply] at he
  change (model P' Q' hP').hom ≫
      (NativeCurrying.derivedEquiv adj H R P' Q' I' hP').symm _ =
    (DerivedCategory.Q.map f ⊗ₘ DerivedCategory.Q.map g) ≫
      ((model P Q hP).hom ≫
        (NativeCurrying.derivedEquiv adj H R P Q I hP).symm φ) ≫ DerivedCategory.Q.map h
  rw [← he, ← Category.assoc, ← hn P' Q' P Q hP' hP g f]
  simp only [Category.assoc]

attribute [local irreducible] representativeEquiv

private noncomputable def representativeIso
    (R : NativeHomRepresentatives ordinaryH H)
    (model : ∀ P Q : CochainComplex (Mod C B) ℤ, ordinaryFlat P →
      (DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj P ≅
        DerivedCategory.Q.obj (ordinaryTotal P Q)))
    (hn : ∀ (P Q P' Q' : CochainComplex (Mod C B) ℤ)
      (hP : ordinaryFlat P) (hP' : ordinaryFlat P') (f : P ⟶ P') (g : Q ⟶ Q'),
      (DerivedCategory.Q.map g ⊗ₘ DerivedCategory.Q.map f) ≫ (model P' Q' hP').hom =
        (model P Q hP).hom ≫ DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g ordinaryBifunctor (.up ℤ))) :
    representativeFunctor (C := C) (B := B) ⋙ CurryingDescent.homHoms H ≅
      representativeFunctor ⋙ CurryingDescent.tensorHoms :=
  NatIso.ofComponents
    (fun X ↦ by
      letI := X.2.2.property
      exact (representativeEquiv H R model X.2.1.unop.obj X.1.unop X.2.2.obj
        X.2.1.unop.property).symm.toIso)
    (fun {X Y} f ↦ by
      let := X.2.2.property
      let := Y.2.2.property
      ext φ
      exact representativeEquiv_naturality H R model hn
        X.2.1.unop.obj Y.2.1.unop.obj X.1.unop Y.1.unop X.2.2.obj Y.2.2.obj
        X.2.1.unop.property Y.2.1.unop.property f.1.unop f.2.1.unop.hom f.2.2.hom φ)

private noncomputable def localizedIso
    (R : NativeHomRepresentatives ordinaryH H)
    (model : ∀ P Q : CochainComplex (Mod C B) ℤ, ordinaryFlat P →
      (DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj P ≅
        DerivedCategory.Q.obj (ordinaryTotal P Q)))
    (hn : ∀ (P Q P' Q' : CochainComplex (Mod C B) ℤ)
      (hP : ordinaryFlat P) (hP' : ordinaryFlat P') (f : P ⟶ P') (g : Q ⟶ Q'),
      (DerivedCategory.Q.map g ⊗ₘ DerivedCategory.Q.map f) ≫ (model P' Q' hP').hom =
        (model P Q hP).hom ≫ DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g ordinaryBifunctor (.up ℤ))) :
    CurryingDescent.homHoms H ≅ CurryingDescent.tensorHoms :=
  (Localization.fullyFaithfulWhiskeringLeft (representativeFunctor (C := C) (B := B))
    representativeW (Type b)).preimageIso (representativeIso H R model hn)

private theorem localizedIso_restrict
    (R : NativeHomRepresentatives ordinaryH H)
    (model : ∀ P Q : CochainComplex (Mod C B) ℤ, ordinaryFlat P →
      (DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj P ≅
        DerivedCategory.Q.obj (ordinaryTotal P Q)))
    (hn : ∀ (P Q P' Q' : CochainComplex (Mod C B) ℤ)
      (hP : ordinaryFlat P) (hP' : ordinaryFlat P') (f : P ⟶ P') (g : Q ⟶ Q'),
      (DerivedCategory.Q.map g ⊗ₘ DerivedCategory.Q.map f) ≫ (model P' Q' hP').hom =
        (model P Q hP).hom ≫ DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g ordinaryBifunctor (.up ℤ))) :
    Functor.isoWhiskerLeft representativeFunctor (localizedIso H R model hn) =
      representativeIso H R model hn := by
  apply Iso.ext
  exact (Localization.fullyFaithfulWhiskeringLeft (representativeFunctor (C := C) (B := B))
    representativeW (Type b)).map_preimage _

attribute [local irreducible] localizedIso

private theorem result
    (R : NativeHomRepresentatives ordinaryH H)
    (model : ∀ P Q : CochainComplex (Mod C B) ℤ, ordinaryFlat P →
      (DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj P ≅
        DerivedCategory.Q.obj (ordinaryTotal P Q)))
    (hn : ∀ (P Q P' Q' : CochainComplex (Mod C B) ℤ)
      (hP : ordinaryFlat P) (hP' : ordinaryFlat P') (f : P ⟶ P') (g : Q ⟶ Q'),
      (DerivedCategory.Q.map g ⊗ₘ DerivedCategory.Q.map f) ≫ (model P' Q' hP').hom =
        (model P Q hP).hom ≫ DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g ordinaryBifunctor (.up ℤ))) :
    ∃ e : ∀ T P I : DerivedCategory (Mod C B),
      (T ⊗ P ⟶ I) ≃ (T ⟶ H.obj (op P, I)),
      (∀ (T T' P P' I I' : DerivedCategory (Mod C B))
        (f : T' ⟶ T) (g : P' ⟶ P) (h : I ⟶ I') (φ : T ⟶ H.obj (op P, I)),
        (e T' P' I').symm (f ≫ φ ≫ H.map (Prod.mkHom g.op h)) =
          (f ⊗ₘ g) ≫ (e T P I).symm φ ≫ h) ∧
      (∀ (P Q I : CochainComplex (Mod C B) ℤ)
        (hP : ordinaryFlat P) (_hQ : ordinaryFlat Q)
        (hI : I.IsKInjective)
        (φ : Q ⟶ CochainComplex.bifunctorHomObj (ordinaryH) P I),
        ∃ ψ : ordinaryTotal P Q ⟶ I,
          (∀ (p q n : ℤ) (hpq : p + q = n),
            HomologicalComplex.ιMapBifunctor P Q (ordinaryBifunctor)
                (.up ℤ) p q n hpq ≫ ψ.f n =
              ((ordinaryBifunctor).obj (P.X p)).map (φ.f q ≫
                  CochainComplex.bifunctorHomπ (ordinaryH) P I q p n hpq) ≫
                (Mod.ihomAdjunction (P.X p)).counit.app (I.X n)) ∧
          (model P Q hP).hom ≫ DerivedCategory.Q.map ψ =
            (e (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P)
              (DerivedCategory.Q.obj I)).symm
                (DerivedCategory.Q.map φ ≫ (R.model P I hI).inv)) := by
  classical
  let e := CurryingDescent.derivedEquiv H (OrdinaryCurrying.localizedIso H R model hn)
  refine ⟨e, ?_, ?_⟩
  · exact CurryingDescent.derivedEquiv_symm_naturality H
      (OrdinaryCurrying.localizedIso H R model hn)
  · intro P Q I hP _hQ hI φ
    let := hI
    let ψ := (NativeCurrying.internalHomEquiv OrdinaryCurrying.adj P I Q).symm φ
    refine ⟨ψ, ?_, ?_⟩
    · intro p q n hpq
      exact NativeCurrying.uncurry_component OrdinaryCurrying.adj P Q I φ p q n hpq
    · have hr := congrArg
        (fun i ↦ i.hom.app
          (op Q, (op (⟨P, hP⟩ : ObjectProperty.FullSubcategory
            (GenericOrdinaryTensor.ordinaryFlat : ObjectProperty
              (CochainComplex (Mod C B) ℤ))),
            (⟨I, hI⟩ : CochainComplex.KInjectives (Mod C B)))))
        (OrdinaryCurrying.localizedIso_restrict H R model hn)
      have he : (e (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P)
            (DerivedCategory.Q.obj I)).symm
              (DerivedCategory.Q.map φ ≫ (R.model P I hI).inv) =
          (OrdinaryCurrying.representativeEquiv H R model P Q I hP).symm
            (DerivedCategory.Q.map φ ≫ (R.model P I hI).inv) :=
        congrArg (fun k ↦ k (DerivedCategory.Q.map φ ≫ (R.model P I hI).inv)) hr
      rw [he, OrdinaryCurrying.representativeEquiv_uncurry]

end OrdinaryCurrying

/-- Product-total Hom representatives determine natural currying bijections for
any natural one-K-flat model of the canonical derived tensor. No adjunction,
closed structure or symmetric structure is included in this statement.

Source: Stacks Tags 08J9, 0A90, 0A8Z and 0A97; ordinary internal-Hom comparison
and uncurrying in step 1 of lem-sf-weil-native-tensor-transport.
(blueprint: lem-sf-native-ordinary-representative-currying).

Proof: use scalar forgetting and the section-ring module equivalence to apply
the ringed-site normalized tensor-Hom bijection. Transport the chain-level
bijection back to native modules. Convert the ringed Hom differential to the
native row convention by multiplying the (n,p) component by (-1)^(np), and reverse
the curried tensor convention. On the summand (p,q), these conversions give the
unsigned counit formula in the conclusion. The chain-map equation is exactly the
Hom cocycle equation, and homotopies correspond. For K-flat P and Q and K-injective
I, both total tensor and product Hom therefore compute the relevant derived Hom
sets. Compose with model and R.model to get the required representative bijection.
The naturality assumption on model and the naturality field of R prove naturality
in all three variables on these representatives. K-flat replacement and K-injective
replacement are localization equivalences, so fully faithful restriction along their
product extends the natural bijection uniquely to all derived objects and maps,
including inverse quasi-isomorphisms. Restricting that extension back to representatives
recovers the bijection used to construct it, proving the final equality. The actual
uncurried chain map gives ψ and its displayed homogeneous counit equation. The source
and target can be zero and the scheme empty; this argument is unbounded throughout. -/
theorem native_ordinary_representative_currying
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (H : (DerivedCategory (ProEtale.AdicSheaf l Y))ᵒᵖ ×
      DerivedCategory (ProEtale.AdicSheaf l Y) ⥤
        DerivedCategory (ProEtale.AdicSheaf l Y))
    (R : NativeHomRepresentatives (ordinaryIhomBifunctor l Y) H)
    (model : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ,
      NativeOrdinaryKFlat l Y P →
        (DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj P ≅
          DerivedCategory.Q.obj (ordinaryTensorTotal l Y P Q)))
    (hn : ∀ (P Q P' Q' : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
      (hP : NativeOrdinaryKFlat l Y P) (hP' : NativeOrdinaryKFlat l Y P')
      (f : P ⟶ P') (g : Q ⟶ Q'),
      (DerivedCategory.Q.map g ⊗ₘ DerivedCategory.Q.map f) ≫ (model P' Q' hP').hom =
        (model P Q hP).hom ≫ DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap f g (ordinaryTensorBifunctor l Y) (.up ℤ))) :
    ∃ e : ∀ T P I : DerivedCategory (ProEtale.AdicSheaf l Y),
      (T ⊗ P ⟶ I) ≃ (T ⟶ H.obj (op P, I)),
      (∀ (T T' P P' I I' : DerivedCategory (ProEtale.AdicSheaf l Y))
        (f : T' ⟶ T) (g : P' ⟶ P) (h : I ⟶ I') (φ : T ⟶ H.obj (op P, I)),
        (e T' P' I').symm (f ≫ φ ≫ H.map (Prod.mkHom g.op h)) =
          (f ⊗ₘ g) ≫ (e T P I).symm φ ≫ h) ∧
      (∀ (P Q I : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
        (hP : NativeOrdinaryKFlat l Y P) (_hQ : NativeOrdinaryKFlat l Y Q)
        (hI : I.IsKInjective)
        (φ : Q ⟶ CochainComplex.bifunctorHomObj (ordinaryIhomBifunctor l Y) P I),
        ∃ ψ : ordinaryTensorTotal l Y P Q ⟶ I,
          (∀ (p q n : ℤ) (hpq : p + q = n),
            HomologicalComplex.ιMapBifunctor P Q (ordinaryTensorBifunctor l Y)
                (.up ℤ) p q n hpq ≫ ψ.f n =
              ((ordinaryTensorBifunctor l Y).obj (P.X p)).map (φ.f q ≫
                  CochainComplex.bifunctorHomπ (ordinaryIhomBifunctor l Y) P I q p n hpq) ≫
                (Mod.ihomAdjunction (P.X p)).counit.app (I.X n)) ∧
          (model P Q hP).hom ≫ DerivedCategory.Q.map ψ =
            (e (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P)
              (DerivedCategory.Q.obj I)).symm
                (DerivedCategory.Q.map φ ≫ (R.model P I hI).inv)) := by
  exact OrdinaryCurrying.result H R model hn

end AlgebraicGeometry.ProEtaleWeilSheaf
