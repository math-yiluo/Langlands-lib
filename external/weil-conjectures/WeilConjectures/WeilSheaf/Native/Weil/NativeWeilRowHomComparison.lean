/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
public import WeilConjectures.CategoryTheory.RingedForgetTwoInjective.RingedForgetTwoInjectiveHom

/-! # Row-sign representatives for the native Hom comparison

Source: Stacks 0A95 and 08J7; native comparison step 4 and step 6
(blueprint: lem-sf-weil-native-row-hom-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open CategoryTheory.RingedForgetTwoInjective

private theorem conjugateLocalizationSquare
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (Q : C ⥤ E) (Q' : D ⥤ F) (U : C ⥤ D) (V : E ⥤ F)
    (δ : Q ⋙ V ≅ U ⋙ Q') {S R : C} {T W : D} {A : E} {B : F}
    (a : A ⟶ Q.obj S) (b : B ⟶ Q'.obj T) (e : V.obj A ⟶ B)
    (c : U.obj S ⟶ T) (s : S ≅ R) (t : T ≅ W)
    (h : e ≫ b = V.map a ≫ δ.hom.app S ≫ Q'.map c) :
    e ≫ (b ≫ Q'.map t.hom) =
      V.map (a ≫ Q.map s.hom) ≫ δ.hom.app R ≫
        Q'.map (U.map s.inv ≫ c ≫ t.hom) := by
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := δ.hom.naturality s.hom
  change V.map (Q.map s.hom) ≫ δ.hom.app R =
    δ.hom.app S ≫ Q'.map (U.map s.hom) at hn
  rw [← Category.assoc (V.map (Q.map s.hom)), hn]
  simp only [Category.assoc]
  rw [← Q'.map_comp_assoc, ← U.map_comp, s.hom_inv_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact (reassoc_of% h) (Q'.map t.hom)

section SignTransport

variable {B : Type*} [Category B] [Abelian B] [HasCountableProducts B]
  (H : Bᵒᵖ ⥤ B ⥤ B) [H.Additive] [∀ P, (H.obj P).Additive]
  (S : StandardModel H) (K I : CochainComplex B ℤ)

private noncomputable def rowDegreeInverse (n : ℤ) :
    (CochainComplex.bifunctorHomObj H K I).X n ⟶ (S.complex.obj (op K, I)).X n :=
  (S.product K I n).lift (Fan.mk _ fun p ↦
    (n * p).negOnePow • CochainComplex.bifunctorHomπ H K I n p (p + n) rfl)

private theorem rowDegreeInverse_projection (n p q : ℤ) (hpq : p + n = q) :
    rowDegreeInverse H S K I n ≫ S.π K I n p q hpq =
      (n * p).negOnePow • CochainComplex.bifunctorHomπ H K I n p q hpq := by
  subst q
  exact (S.product K I n).fac _ ⟨p⟩

private noncomputable def rowDegreeIso (n : ℤ) :
    (S.complex.obj (op K, I)).X n ≅ (CochainComplex.bifunctorHomObj H K I).X n where
  hom := CochainComplex.bifunctorHomLift H K I n fun p q hpq ↦
    (n * p).negOnePow • S.π K I n p q hpq
  inv := rowDegreeInverse H S K I n
  hom_inv_id := by
    apply Fan.IsLimit.hom_ext (S.product K I n)
    intro p
    rw [Category.assoc]
    change _ ≫ _ ≫ S.π K I n p (p + n) rfl = _
    rw [rowDegreeInverse_projection, Linear.comp_units_smul,
      CochainComplex.bifunctorHomLift_π, smul_smul, Int.units_mul_self, one_smul]
    exact (Category.id_comp _).symm
  inv_hom_id := by
    apply CochainComplex.bifunctorHomObj_hom_ext
    intro p q hpq
    rw [Category.assoc, CochainComplex.bifunctorHomLift_π,
      Linear.comp_units_smul, rowDegreeInverse_projection,
      smul_smul, Int.units_mul_self, one_smul, Category.id_comp]

private theorem rowDegreeIso_hom_projection (n p q : ℤ) (hpq : p + n = q) :
    (rowDegreeIso H S K I n).hom ≫ CochainComplex.bifunctorHomπ H K I n p q hpq =
      (n * p).negOnePow • S.π K I n p q hpq := by
  simp [rowDegreeIso]

private noncomputable def rowIso :
    S.complex.obj (op K, I) ≅ CochainComplex.bifunctorHomObj H K I :=
  HomologicalComplex.Hom.isoOfComponents (rowDegreeIso H S K I) (by
    intro n m hnm
    apply CochainComplex.bifunctorHomObj_hom_ext
    intro p q hpq
    have hnm' : n + 1 = m := hnm
    rw [Category.assoc, CochainComplex.bifunctorHomObj_d_π H K I n m p q hpq
      (p + n) (p + 1) rfl (by lia)]
    rw [Linear.comp_units_smul, Preadditive.comp_sub]
    rw [← Category.assoc, rowDegreeIso_hom_projection]
    rw [← Category.assoc, rowDegreeIso_hom_projection]
    rw [Category.assoc, rowDegreeIso_hom_projection, Linear.comp_units_smul]
    rw [S.differential K I n m p q (p + n) (p + 1) hnm' hpq rfl (by lia)]
    subst m
    simp only [smul_sub, Linear.units_smul_comp, smul_smul]
    have h₁ : ((n + 1) * p).negOnePow = p.negOnePow * (n * p).negOnePow := by
      rw [Int.add_mul, one_mul, Int.negOnePow_add, mul_comm]
    have h₂ : ((n + 1) * p).negOnePow * n.negOnePow =
        p.negOnePow * (n * (p + 1)).negOnePow := by
      rw [h₁, Int.mul_add, mul_one, Int.negOnePow_add, mul_assoc]
    rw [h₂, h₁])

private theorem rowIso_hom_projection (n p q : ℤ) (hpq : p + n = q) :
    (rowIso H S K I).hom.f n ≫ CochainComplex.bifunctorHomπ H K I n p q hpq =
      (n * p).negOnePow • S.π K I n p q hpq :=
  rowDegreeIso_hom_projection H S K I n p q hpq

private theorem rowIso_naturality (K' I' : CochainComplex B ℤ)
    (f : K' ⟶ K) (g : I ⟶ I') :
    S.complex.map (X := (op K, I)) (Y := (op K', I')) (f.op, g) ≫
        (rowIso H S K' I').hom =
      (rowIso H S K I).hom ≫
        (CochainComplex.bifunctorHomMapLeft (H := H) (Y := I) f ≫
          CochainComplex.bifunctorHomMapRight (H := H) (K := K') g) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply CochainComplex.bifunctorHomObj_hom_ext
  intro p q hpq
  simp only [HomologicalComplex.comp_f, Category.assoc,
    rowIso_hom_projection, Linear.comp_units_smul,
    CochainComplex.bifunctorHomMapRight_f_π,
    CochainComplex.bifunctorHomMapLeft_f_π_assoc]
  rw [← Category.assoc, rowIso_hom_projection]
  simp only [Linear.units_smul_comp]
  rw [S.map_projection]

variable [HasDerivedCategory B]

private noncomputable def rowRepresentatives
    (D : (DerivedCategory B)ᵒᵖ × DerivedCategory B ⥤ DerivedCategory B)
    (R : Representatives S.complex D) :
    AlgebraicGeometry.ProEtaleWeilSheaf.NativeHomRepresentatives H D where
  model K I hI :=
    letI := hI
    R.iso K I ≪≫ DerivedCategory.Q.mapIso (rowIso H S K I)
  naturality P P' I I' hI hI' f g := by
    let _ := hI
    let _ := hI'
    dsimp only [Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, R.naturality, Category.assoc, ← Functor.map_comp,
      rowIso_naturality, Functor.map_comp, Category.assoc]

variable [Abelian.HasKInjectiveResolutions B]

private noncomputable def sliceModel
    (D : (DerivedCategory B)ᵒᵖ × DerivedCategory B ⥤ DerivedCategory B)
    (R : AlgebraicGeometry.ProEtaleWeilSheaf.NativeHomRepresentatives H D)
    (L : DerivedCategory B) :
    Prod.sectL (DerivedCategory B)ᵒᵖ L ⋙ D ≅ DerivedCategory.bifunctorRHom H L := by
  let E := (HomotopyCategory.KInjectives.Qh (C := B)).asEquivalence
  let I := DerivedCategory.kInjectiveRep L
  let F := (Prod.sectL (DerivedCategory B)ᵒᵖ L ⋙ D).rightOp
  let G := HomotopyCategory.KInjectives.ι ⋙ CochainComplex.bifunctorHomHomotopyFunctor H I
  let e (J : HomotopyCategory.KInjectives B) :
      D.obj (op (E.functor.obj J), L) ≅
        DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (.up ℤ)).obj
          (CochainComplex.bifunctorHomObj H J.obj.as I)) := by
    have : CochainComplex.IsKInjective J.obj.as := by
      rw [CochainComplex.isKInjective_iff_rightOrthogonal]
      exact J.property
    exact D.mapIso
      (((DerivedCategory.quotientCompQhIso B).app J.obj.as).symm.op.prod
        (DerivedCategory.kInjectiveRepIso L)) ≪≫ R.model J.obj.as I inferInstance ≪≫
      ((DerivedCategory.quotientCompQhIso B).app _).symm
  let pre : E.functor ⋙ F ≅ G := NatIso.ofComponents (fun J ↦ (e J).symm.op) (by
    intro J J' f
    apply Quiver.Hom.unop_inj
    change (e J').inv ≫ D.map ((E.functor.map f).op, 𝟙 L) =
      (G.map f).unop ≫ (e J).inv
    apply (cancel_epi (e J').hom).1
    apply (Iso.cancel_iso_hom_right _ _ (e J)).1
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
    let a := (DerivedCategory.quotientCompQhIso B).app J.obj.as
    let b := (DerivedCategory.quotientCompQhIso B).app J'.obj.as
    let j := DerivedCategory.kInjectiveRepIso L
    have hq : a.inv ≫ E.functor.map f = DerivedCategory.Q.map f.hom.out ≫ b.inv := by
      change a.inv ≫ DerivedCategory.Qh.map f.hom = _
      have h := ((DerivedCategory.quotientCompQhIso B).inv.naturality f.hom.out).symm
      dsimp only [CategoryTheory.Functor.comp_map] at h
      rw [HomotopyCategory.quotient_map_out] at h
      exact h
    have hd : D.map ((E.functor.map f).op, 𝟙 L) ≫
          (D.mapIso (a.symm.op.prod j)).hom =
        (D.mapIso (b.symm.op.prod j)).hom ≫
          D.map ((DerivedCategory.Q.map f.hom.out).op, 𝟙 (DerivedCategory.Q.obj I)) := by
      simp only [Functor.mapIso_hom, ← D.map_comp]
      congr 1
      apply Prod.ext
      · exact congrArg Quiver.Hom.op hq
      · change (𝟙 L) ≫ j.hom = j.hom ≫ (𝟙 _)
        exact (Category.id_comp _).trans (Category.comp_id _).symm
    have : CochainComplex.IsKInjective J.obj.as := by
      rw [CochainComplex.isKInjective_iff_rightOrthogonal]
      exact J.property
    have : CochainComplex.IsKInjective J'.obj.as := by
      rw [CochainComplex.isKInjective_iff_rightOrthogonal]
      exact J'.property
    have hr := R.naturality J.obj.as J'.obj.as I I inferInstance inferInstance
      f.hom.out (𝟙 I)
    simp only [CategoryTheory.Functor.map_id, CochainComplex.bifunctorHomMapRight_id,
      Category.comp_id] at hr
    have ht := (DerivedCategory.quotientCompQhIso B).inv.naturality
      (CochainComplex.bifunctorHomMapLeft (H := H) (Y := I) f.hom.out)
    change D.map ((E.functor.map f).op, 𝟙 L) ≫
      (D.mapIso (a.symm.op.prod j)).hom ≫ (R.model J.obj.as I inferInstance).hom ≫ _ =
      ((D.mapIso (b.symm.op.prod j)).hom ≫
        (R.model J'.obj.as I inferInstance).hom ≫ _) ≫ _
    rw [← Category.assoc, hd, Category.assoc]
    rw [reassoc_of% hr]
    change _ ≫ _ ≫ (DerivedCategory.Q.map _ ≫
      (DerivedCategory.quotientCompQhIso B).inv.app _) = _
    rw [ht]
    simp only [Category.assoc]
    have hg : (G.map f).unop = DerivedCategory.Qh.map
        ((HomotopyCategory.quotient B (.up ℤ)).map
          (CochainComplex.bifunctorHomMapLeft (H := H) (Y := I) f.hom.out)) := by
      change ((CochainComplex.bifunctorHomHomotopyFunctor H I).map f.hom).unop = _
      conv_lhs => rw [← HomotopyCategory.quotient_map_out f.hom]
      rw [CochainComplex.bifunctorHomHomotopyFunctor_map]
      rfl
    rw [hg]
    rfl)
  let t : F ≅ E.inverse ⋙ G :=
    (Functor.isoWhiskerRight E.counitIso F).symm ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft E.inverse pre
  let t' : F.leftOp ≅ (E.inverse ⋙ G).leftOp :=
    NatIso.ofComponents (fun X ↦ (t.app X.unop).symm.unop) (by
      intro X Y f
      exact (congrArg Quiver.Hom.unop (t.inv.naturality f.unop)).symm)
  exact (Functor.rightOpLeftOpIso _).symm ≪≫ t'

end SignTransport

namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

private theorem rowCompatibility
    (m : TwoInjectiveHomModel (k₀ := k₀) (l := l) (X := X)) :
    NativeHomRepresentativeCompatibility (ihomBifunctor k₀ l X)
      (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      m.hom m.underlyingHom
      (rowRepresentatives _ m.source m.hom m.representatives)
      (rowRepresentatives (ordinaryIhomBifunctor l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        m.target m.underlyingHom m.underlyingRepresentatives)
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) m.derived := by
  let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
  let UC := U.mapHomologicalComplex (.up ℤ)
  let _ := forgetKInjective (k₀ := k₀) (l := l) (X := X)
  intro P I hP hI
  let _ := hP
  let _ := hI
  let s := rowIso (ihomBifunctor k₀ l X) m.source P I
  let t := rowIso (ordinaryIhomBifunctor l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) m.target (UC.obj P) (UC.obj I)
  let χ := (UC.mapIso s).symm ≪≫ m.chain.app (op P, I) ≪≫ t
  refine ⟨inferInstance, inferInstance, χ, ?_, ?_⟩
  · intro n p q hpq
    apply heq_of_eq
    change ((UC.map s.inv ≫ (m.chain.app (op P, I)).hom) ≫ t.hom).f n ≫ _ = _
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc,
      Category.assoc, rowIso_hom_projection, Linear.comp_units_smul]
    rw [Linear.comp_units_smul]
    change (n * p).negOnePow • ((UC.map s.inv).f n ≫
      (m.chain.hom.app (op P, I)).f n ≫ m.target.π (UC.obj P) (UC.obj I) n p q hpq) = _
    rw [m.chain_projection P I n p q hpq]
    change (n * p).negOnePow •
      (U.map (s.inv.f n) ≫ (U.map (m.source.π P I n p q hpq) ≫ _)) = _
    rw [← Category.assoc, ← U.map_comp]
    change (n * p).negOnePow •
      (U.map (rowDegreeInverse _ m.source P I n ≫ m.source.π P I n p q hpq) ≫ _) = _
    rw [rowDegreeInverse_projection]
    simp only [Units.smul_def, U.map_zsmul, Preadditive.zsmul_comp, smul_smul,
      ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
    rfl
  · have h := m.derived_representative P I
    change _ ≫ _ ≫
      ((m.underlyingRepresentatives.iso (UC.obj P) (UC.obj I)).hom ≫
        DerivedCategory.Q.map t.hom) =
      U.mapDerivedCategory.map
        ((m.representatives.iso P I).hom ≫ DerivedCategory.Q.map s.hom) ≫
        U.mapDerivedCategoryFactors.hom.app _ ≫
          DerivedCategory.Q.map (UC.map s.inv ≫ (m.chain.app (op P, I)).hom ≫ t.hom)
    simpa only [U, UC, Iso.app_hom, Prod.mkHom, Category.assoc] using
      conjugateLocalizationSquare DerivedCategory.Q DerivedCategory.Q UC
      U.mapDerivedCategory U.mapDerivedCategoryFactors
      (m.representatives.iso P I).hom
      (m.underlyingRepresentatives.iso (UC.obj P) (UC.obj I)).hom
      (m.derived.hom.app (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I) ≫
        m.underlyingHom.map
          ((U.mapDerivedCategoryFactors.inv.app P).op,
            U.mapDerivedCategoryFactors.hom.app I))
      (m.chain.app (op P, I)).hom s t (by simpa only [U, UC, Iso.app_hom, Category.assoc] using h)

private noncomputable def rowClosedModel
    (m : TwoInjectiveHomModel (k₀ := k₀) (l := l) (X := X)) :
    NativeClosedHomModels k₀ l X where
  weilHom := m.hom
  ordinaryHom := m.underlyingHom
  nativeModel := m.native
  ordinaryModel := sliceModel
    (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    m.underlyingHom (rowRepresentatives
      (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      m.target m.underlyingHom m.underlyingRepresentatives)
  weilRepresentatives := rowRepresentatives (ihomBifunctor k₀ l X)
    m.source m.hom m.representatives
  ordinaryRepresentatives := rowRepresentatives
    (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    m.target m.underlyingHom m.underlyingRepresentatives

/- Convert the supplied standard-sign two-injective comparison to row-sign
representatives in the native and ordinary module categories.

Source: Stacks 0A95 and 08J7; the native comparison proof, steps 4 and 6,
and the sign normalization in TwoInjectiveHomModel
(blueprint: lem-sf-weil-native-row-hom-comparison).

Proof: keep m.hom, m.underlyingHom and m.derived. Compose each representative
isomorphism with the inverse of the native-to-standard sign map. On the
ordinary side construct that sign map projectionwise by multiplying degree n,
source index p by (-1)^(n*p). The product universal property constructs both
maps. The standard differential equation and the row-sign equation show they
are chain maps; the square is the identity. This is the same sign computation
as m.sign_projection, on ordinary modules. Naturality follows on every product
projection. On source slices the original native identification is m.native;
on ordinary slices compare the chosen K-injective target and source with the
recorded bifunctorRHom via their resolution quasi-isomorphisms. Their localized
Hom maps are invertible, so the comparison is natural on all derived arrows.
Finally conjugate m.chain by the two sign maps. Forgetting preserves the integer
scalar, so the signs cancel on each projection, giving the stated HEq. Conjugate
m.derived_representative by these same maps; its localization factors are
unchanged. This gives NativeHomRepresentativeCompatibility for m.derived. -/
/-- Transport both standard-sign representative systems to row-sign systems.
The comparison is the supplied derived comparison itself; only its representative
systems and its chain-level square are conjugated by the sign isomorphisms.

Source: Stacks 0A95 and 08J7; native comparison proof, steps 4 and 6
(blueprint: lem-sf-weil-native-row-hom-comparison).
-/
theorem native_row_hom_data
    (m : TwoInjectiveHomModel (k₀ := k₀) (l := l) (X := X)) :
    ∃ M : NativeClosedHomModels k₀ l X,
    ∃ η : M.weilHom ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).op.prod (nativeForget k₀ l X) ⋙ M.ordinaryHom,
      HEq M.weilHom m.hom ∧ HEq M.ordinaryHom m.underlyingHom ∧
      NativeHomRepresentativeCompatibility (ihomBifunctor k₀ l X)
        (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        M.weilHom M.ordinaryHom M.weilRepresentatives M.ordinaryRepresentatives
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) η := by
  exact ⟨rowClosedModel k₀ l X m, m.derived, HEq.rfl, HEq.rfl,
    rowCompatibility k₀ l X m⟩

/- STATEMENT-DISPUTED: the former native_row_hom_eta_eq allowed arbitrary
representative isomorphisms. Negating the native representative and the derived
comparison preserves its hypotheses but changes the comparison on a nonzero Hom.
The false assertion is withdrawn. The construction below uses m.derived itself,
so its equality clause is reflexive; it needs no uniqueness assertion. -/

theorem native_row_hom_comparison
    (m : TwoInjectiveHomModel (k₀ := k₀) (l := l) (X := X)) :
    ∃ M : NativeClosedHomModels k₀ l X,
    ∃ η : M.weilHom ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).op.prod (nativeForget k₀ l X) ⋙ M.ordinaryHom,
      HEq M.weilHom m.hom ∧ HEq M.ordinaryHom m.underlyingHom ∧ HEq η m.derived ∧
      NativeHomRepresentativeCompatibility (ihomBifunctor k₀ l X)
        (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        M.weilHom M.ordinaryHom M.weilRepresentatives M.ordinaryRepresentatives
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) η := by
  exact ⟨rowClosedModel k₀ l X m, m.derived, HEq.rfl, HEq.rfl, HEq.rfl,
    rowCompatibility k₀ l X m⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
