/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.DerivedHom
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact
import WeilConjectures.WeilSheaf.DerivedHomPrecomposition

/-! # Single-source computation of native Weil derived internal Hom

Source: Stacks Project, Tag 0A95, equivariant analogue; native models in
`WeilConjectures.WeilSheaf.DerivedHom` and `WeilConjectures.WeilSheaf.Fourier`
(used for `proposition-six-operations-dctf--15`).

The projection to source degree zero is specified on complexes. The comparison below
is normalized by precomposition for every K-injective resolution of the source.
Naturality in the target is stated on K-injective representatives, where every derived
morphism has a chain representative, unique up to homotopy.

The upstream product-Hom differential uses the row sign (-1)^p. Its canonical
identification with d(f) = d_I f - (-1)^n f d_J multiplies the (p,n) component by
(-1)^(p*n). This identification is natural in both complexes and is the identity
on p = 0, so it preserves the precomposition and single-source normalization.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtaleWeilSheaf.SingleResolutionAux
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

end AlgebraicGeometry.ProEtaleWeilSheaf.SingleResolutionAux

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
  [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- Projection to source degree zero commutes with the differentials.
Source: Stacks Tag 0A95, degree-zero specialization
(used for `proposition-six-operations-dctf--15`).

Proof: in the product-Hom differential the source differential is zero. Projection
onto p = 0 leaves only postcomposition with the target differential; its sign is +1.
The single-complex identification transports its degree-zero source to A. -/
theorem singleResolutionProjection_comm (A : ProEtaleWeilSheaf k₀ l X)
    (I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) (n m : ℤ) :
    (CochainComplex.bifunctorHomπ (ihomBifunctor k₀ l X)
        ((CochainComplex.singleFunctor _ 0).obj A) I n 0 n (zero_add n) ≫
      ((ihomBifunctor k₀ l X).map
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv.op).app (I.X n)) ≫
        (((ihomFunctor k₀ l X A).mapHomologicalComplex (.up ℤ)).obj I).d n m =
    (CochainComplex.bifunctorHomObj (ihomBifunctor k₀ l X)
        ((CochainComplex.singleFunctor _ 0).obj A) I).d n m ≫
      (CochainComplex.bifunctorHomπ (ihomBifunctor k₀ l X)
          ((CochainComplex.singleFunctor _ 0).obj A) I m 0 m (zero_add m) ≫
        ((ihomBifunctor k₀ l X).map
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv.op).app (I.X m)) := by
  rw [Category.assoc,
    CochainComplex.bifunctorHomObj_d_π_assoc _ _ _ n m 0 m (zero_add m) n
      (m - n) (zero_add n) (by omega)]
  simp only [CochainComplex.singleFunctor_obj_d, op_zero, Functor.map_zero,
    NatTrans.app_zero, comp_zero, sub_zero, Int.negOnePow_zero, one_smul,
    Functor.mapHomologicalComplex_obj_d, Category.assoc]
  exact congrArg (CochainComplex.bifunctorHomπ (ihomBifunctor k₀ l X)
    ((CochainComplex.singleFunctor _ 0).obj A) I n 0 n (zero_add n) ≫ ·)
    (((ihomBifunctor k₀ l X).map
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv.op).naturality (I.d n m)).symm

/-- The canonical projection from the Hom complex with source A[0] to termwise H_A.
Source: Stacks Tag 0A95, degree-zero specialization
(used for `proposition-six-operations-dctf--15`). -/
noncomputable def singleResolutionProjection (A : ProEtaleWeilSheaf k₀ l X)
    (I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    CochainComplex.bifunctorHomObj (ihomBifunctor k₀ l X)
        ((CochainComplex.singleFunctor _ 0).obj A) I ⟶
      ((ihomFunctor k₀ l X A).mapHomologicalComplex (.up ℤ)).obj I where
  f n := CochainComplex.bifunctorHomπ (ihomBifunctor k₀ l X)
      ((CochainComplex.singleFunctor _ 0).obj A) I n 0 n (zero_add n) ≫
    ((ihomBifunctor k₀ l X).map
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv.op).app (I.X n)
  comm' n m _ := singleResolutionProjection_comm A I n m

/-- Projection to source degree zero is a chain isomorphism.
Source: Stacks Tag 0A95, degree-zero specialization
(used for `proposition-six-operations-dctf--15`).

Proof: every factor with p ≠ 0 is H(0,I^(p+n)), hence zero. The inverse inserts the
chosen section in the p = 0 factor and zero in every other factor. The product
universal property verifies the two inverse identities degree by degree. -/
theorem singleResolutionProjection_isIso (A : ProEtaleWeilSheaf k₀ l X)
    (I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    IsIso (singleResolutionProjection A I) := by
  classical
  have : ∀ n, IsIso ((singleResolutionProjection A I).f n) := by
    intro n
    let j : (((ihomFunctor k₀ l X A).mapHomologicalComplex (.up ℤ)).obj I).X n ⟶
        (CochainComplex.bifunctorHomObj (ihomBifunctor k₀ l X)
          ((CochainComplex.singleFunctor _ 0).obj A) I).X n :=
      CochainComplex.bifunctorHomLift _ _ _ n fun p q hpq ↦
        if h : p = 0 then by
          subst p
          simp only [zero_add] at hpq
          cases (show q = n by omega)
          exact ((ihomBifunctor k₀ l X).map
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom.op).app (I.X n)
        else 0
    refine ⟨⟨j, ?_, ?_⟩⟩
    · apply CochainComplex.bifunctorHomObj_hom_ext
      intro p q hpq
      by_cases h : p = 0
      · subst p
        simp only [zero_add] at hpq
        cases (show q = n by omega)
        simp only [singleResolutionProjection, j, Category.assoc,
          CochainComplex.bifunctorHomLift_π, ↓reduceDIte, ← NatTrans.comp_app,
          ← Functor.map_comp, ← op_comp, Iso.hom_inv_id, op_id,
          (ihomBifunctor k₀ l X).map_id, NatTrans.id_app, Category.id_comp]
        erw [Category.comp_id]
      · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 A p h
        have hz' := ((evaluation _ _).obj (I.X q)).map_isZero
          ((ihomBifunctor k₀ l X).map_isZero hz.op)
        exact hz'.eq_of_tgt _ _
    · simp [singleResolutionProjection, j, ← NatTrans.comp_app,
        ← Functor.map_comp, ← op_comp]
      rfl
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Postcomposition on the native Hom model, before replacing the target.
The source is the same chosen K-injective object used by bifunctorRHomOfComplex.
Source: native bifunctor in BifunctorHom.lean, Tags 070I and 0A95
(used for `proposition-six-operations-dctf--15`). -/
noncomputable def singleResolutionMapRight (A : ProEtaleWeilSheaf k₀ l X)
    {I I' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ} (g : I ⟶ I') :
    (DerivedCategory.bifunctorRHomOfComplex (ihomBifunctor k₀ l X) I).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj A)) ⟶
      (DerivedCategory.bifunctorRHomOfComplex (ihomBifunctor k₀ l X) I').obj
        (op ((DerivedCategory.singleFunctor _ 0).obj A)) :=
  DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
    (CochainComplex.bifunctorHomMapRight
      (H := ihomBifunctor k₀ l X)
      (K := (((HomotopyCategory.KInjectives.Qh
        (C := ProEtaleWeilSheaf k₀ l X)).inv.obj
          ((DerivedCategory.singleFunctor _ 0).obj A)).obj).as) g))

private lemma projection_left (A B : ProEtaleWeilSheaf k₀ l X) (a : A ⟶ B)
    (I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    CochainComplex.bifunctorHomMapLeft (H := ihomBifunctor k₀ l X) (Y := I)
        ((CochainComplex.singleFunctor _ 0).map a) ≫ singleResolutionProjection A I =
      singleResolutionProjection B I ≫
        (NatTrans.mapHomologicalComplex ((ihomBifunctor k₀ l X).map a.op) (.up ℤ)).app I := by
  apply HomologicalComplex.Hom.ext
  funext n
  dsimp only [HomologicalComplex.comp_f, singleResolutionProjection]
  rw [Category.assoc, CochainComplex.bifunctorHomMapLeft_f_π_assoc]
  change _ ≫ ((ihomBifunctor k₀ l X).map
    (((CochainComplex.singleFunctor _ 0).map a).f 0).op).app (I.X n) ≫ _ =
    _ ≫ _ ≫ ((ihomBifunctor k₀ l X).map a.op).app (I.X n)
  rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp]
  rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp]
  congr 3

private lemma projection_right (A : ProEtaleWeilSheaf k₀ l X)
    {I I' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ} (g : I ⟶ I') :
    CochainComplex.bifunctorHomMapRight (H := ihomBifunctor k₀ l X)
        (K := (CochainComplex.singleFunctor _ 0).obj A) g ≫
        singleResolutionProjection A I' =
      singleResolutionProjection A I ≫
        ((ihomFunctor k₀ l X A).mapHomologicalComplex (.up ℤ)).map g := by
  apply HomologicalComplex.Hom.ext
  funext n
  dsimp only [HomologicalComplex.comp_f, singleResolutionProjection]
  rw [Category.assoc, CochainComplex.bifunctorHomMapRight_f_π_assoc]
  simp only [Functor.mapHomologicalComplex_map_f]
  exact congrArg (CochainComplex.bifunctorHomπ (ihomBifunctor k₀ l X)
    ((CochainComplex.singleFunctor _ 0).obj A) I n 0 n (zero_add n) ≫ ·)
    (((ihomBifunctor k₀ l X).map
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv.op).naturality (g.f n))

private noncomputable def resolutionComparison (A : ProEtaleWeilSheaf k₀ l X)
    (I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) [I.IsKInjective]
    (h : IsIso (SingleResolutionAux.comparison (ihomBifunctor k₀ l X)
      ((CochainComplex.singleFunctor _ 0).obj A) I)) :
    (DerivedCategory.bifunctorRHomOfComplex (ihomBifunctor k₀ l X) I).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj A)) ≅
      (ihomFunctor k₀ l X A).rightDerivedFunctor.obj (DerivedCategory.Q.obj I) :=
  letI := h
  letI := singleResolutionProjection_isIso A I
  asIso (SingleResolutionAux.comparison (ihomBifunctor k₀ l X)
    ((CochainComplex.singleFunctor _ 0).obj A) I) ≪≫
    DerivedCategory.Q.mapIso (asIso (singleResolutionProjection A I)) ≪≫
    ((ihomFunctor k₀ l X A).rightDerivedFunctorObjQIso I).symm

private lemma resolutionComparison_hom (A : ProEtaleWeilSheaf k₀ l X)
    (I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) [I.IsKInjective]
    (h : IsIso (SingleResolutionAux.comparison (ihomBifunctor k₀ l X)
      ((CochainComplex.singleFunctor _ 0).obj A) I)) :
    (resolutionComparison A I h).hom =
      SingleResolutionAux.comparison (ihomBifunctor k₀ l X)
        ((CochainComplex.singleFunctor _ 0).obj A) I ≫
      DerivedCategory.Q.map (singleResolutionProjection A I) ≫
      ((ihomFunctor k₀ l X A).rightDerivedFunctorObjQIso I).inv := rfl

/-- Native derived internal Hom from A[0] is the total right derived functor of H_A.
The comparison is represented by precomposition with every K-injective resolution
of A[0], followed by the canonical source-degree-zero projection. It is independent
of the resolutions and natural contravariantly in A and covariantly in the target.
Source: Stacks Tag 0A95, equivariant analogue, and Tags 08BJ, 070I, 070K
(used for `proposition-six-operations-dctf--15`).

Proof:
1. For T = Frobenius pullback, the fixed-pair forgetful functor U is faithful and
   exact, creates products and detects quasi-isomorphisms. T is an exact equivalence;
   kernels, cokernels and products carry the induced invertible structure maps.
2. On underlying module sheaves form L(M) = coproduct over n in Z of T^n M, with
   structure given by the successor identifications and reindexing n to n+1.
3. Restriction to n=0 gives Hom(L(M),F) = Hom(M,U(F)). Its inverse extends a map
   recursively by the invertible structure of F in both directions. The recursions
   give equivariance, the inverse identities and naturality; thus L is left adjoint to U.
4. L is exact: each T^n is exact, and its coproduct is the filtered colimit of finite
   direct sums. Module sheaves have exact filtered colimits by
   lem-pur-ringed-site-grothendieck-abelian. Apply
   lem-weil-pbc-right-adjoint-preserves-kinjective to conclude U(I) is K-injective.
5. Precomposition with alpha is an equivariant chain map. Its underlying map is
   the ringed-site Hom-complex map of lem-pur-rhom-well-defined (Tag 0A95), hence
   a quasi-isomorphism. U reflects this, and Q inverts it.
6. Projection to p=0 identifies Hom(A[0],I) with H_A(I), as specified above.
   The fixed-pair category is Grothendieck: U creates colimits, filtered colimits
   are exact, and L of a generator generates by the adjunction and faithfulness.
   prose-03-02 supplies resolutions. The termwise K-injective
   computation of def-sfb-right-derived-functor identifies Q(H_A(I)) with RH_A(QI).
7. By lem-weil-pbc-kinjective-hom-derived, derived arrows into K-injectives are
   represented by chain maps unique up to homotopy. The comparison for two source
   resolutions agrees since precomposition by their homotopy comparison commutes
   with alpha after localization. Target changes commute by associativity. A source
   homotopy induces the Hom homotopy f ↦ (-1)^n f h; a target homotopy gives f ↦ h'f.
   These prove independence and both naturality squares on K-injective representatives,
   hence on the derived category. Transport along kInjectiveRepIso gives the final
   clause for arbitrary bounded-below N. No lissity or constructibility is used. -/
theorem derivedHom_single_resolution
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    ∃ c : ∀ (A : ProEtaleWeilSheaf k₀ l X)
      (I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) [I.IsKInjective],
      (∃ b : ℤ, (DerivedCategory.Q.obj I).IsGE b) →
      ((DerivedCategory.bifunctorRHomOfComplex (ihomBifunctor k₀ l X) I).obj
          (op ((DerivedCategory.singleFunctor _ 0).obj A)) ≅
        (ihomFunctor k₀ l X A).rightDerivedFunctor.obj (DerivedCategory.Q.obj I)),
    (∀ (A : ProEtaleWeilSheaf k₀ l X)
      (I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) [I.IsKInjective]
      (hI : ∃ b : ℤ, (DerivedCategory.Q.obj I).IsGE b)
      (J : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) [J.IsKInjective]
      (α : (CochainComplex.singleFunctor _ 0).obj A ⟶ J) [QuasiIso α],
      (c A I hI).hom ≫ ((ihomFunctor k₀ l X A).rightDerivedFunctorObjQIso I).hom =
        (DerivedCategory.bifunctorRHomOfComplex (ihomBifunctor k₀ l X) I).map
            (inv (DerivedCategory.Q.map α)).op ≫
          (DerivedCategory.bifunctorRHomOfComplexObjIso (ihomBifunctor k₀ l X) I J).hom ≫
          DerivedCategory.Q.map
            (CochainComplex.bifunctorHomMapLeft (H := ihomBifunctor k₀ l X) (Y := I) α) ≫
          DerivedCategory.Q.map (singleResolutionProjection A I)) ∧
    (∀ (A B : ProEtaleWeilSheaf k₀ l X) (a : A ⟶ B)
      (I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) [I.IsKInjective]
      (hI : ∃ b : ℤ, (DerivedCategory.Q.obj I).IsGE b),
      (DerivedCategory.bifunctorRHomOfComplex (ihomBifunctor k₀ l X) I).map
          ((DerivedCategory.singleFunctor _ 0).map a).op ≫ (c A I hI).hom =
        (c B I hI).hom ≫
          (Functor.rightDerivedFunctorNatTrans ((ihomBifunctor k₀ l X).map a.op)).app
            (DerivedCategory.Q.obj I)) ∧
    (∀ (A : ProEtaleWeilSheaf k₀ l X)
      (I I' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      [I.IsKInjective] [I'.IsKInjective]
      (hI : ∃ b : ℤ, (DerivedCategory.Q.obj I).IsGE b)
      (hI' : ∃ b : ℤ, (DerivedCategory.Q.obj I').IsGE b) (g : I ⟶ I'),
      singleResolutionMapRight A g ≫ (c A I' hI').hom =
        (c A I hI).hom ≫ (ihomFunctor k₀ l X A).rightDerivedFunctor.map
          (DerivedCategory.Q.map g)) ∧
    (∀ (A : ProEtaleWeilSheaf k₀ l X)
      (N : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) (_ : ∃ b : ℤ, N.IsGE b),
      ∃ e : (derivedHom k₀ l X N).obj (op ((DerivedCategory.singleFunctor _ 0).obj A)) ≅
        (ihomFunctor k₀ l X A).rightDerivedFunctor.obj N,
      ∀ hI : ∃ b : ℤ, (DerivedCategory.Q.obj (DerivedCategory.kInjectiveRep N)).IsGE b,
        e.hom ≫ (ihomFunctor k₀ l X A).rightDerivedFunctor.map
            (DerivedCategory.kInjectiveRepIso N).hom =
          (c A (DerivedCategory.kInjectiveRep N) hI).hom) := by
  classical
  have hi (A : ProEtaleWeilSheaf k₀ l X)
      (I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) [I.IsKInjective] :
      IsIso (SingleResolutionAux.comparison (ihomBifunctor k₀ l X)
        ((CochainComplex.singleFunctor _ 0).obj A) I) := by
    apply SingleResolutionAux.comparison_isIso
    intro J _ a _
    have := quasiIso_bifunctorHomMapLeft (I := I) a
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr inferInstance
  let c (A : ProEtaleWeilSheaf k₀ l X)
      (I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) [I.IsKInjective]
      (_ : ∃ b : ℤ, (DerivedCategory.Q.obj I).IsGE b) :=
    resolutionComparison A I (hi A I)
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · intro A I _ hI J _ α _
    simpa only [c, resolutionComparison_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] using
      congrArg (· ≫ DerivedCategory.Q.map (singleResolutionProjection A I))
        (SingleResolutionAux.comparison_resolution (ihomBifunctor k₀ l X)
          ((CochainComplex.singleFunctor _ 0).obj A) I J α)
  · intro A B a I _ hI
    have hC := CommSq.mk (SingleResolutionAux.comparison_naturality
      (ihomBifunctor k₀ l X) ((CochainComplex.singleFunctor _ 0).map a) I)
    have hP := (CommSq.mk (projection_left A B a I)).map DerivedCategory.Q
    have hR := (CommSq.mk (Functor.rightDerivedFunctorNatTrans_app_Q_obj
      ((ihomBifunctor k₀ l X).map a.op) I)).vert_inv
    simp only [c, resolutionComparison_hom]
    exact (hC.vert_comp (hP.vert_comp hR)).w
  · intro A I I' _ _ hI hI' g
    have hC := CommSq.mk (SingleResolutionAux.comparison_right (ihomBifunctor k₀ l X) g
      ((CochainComplex.singleFunctor _ 0).obj A))
    have hP := (CommSq.mk (projection_right A g)).map DerivedCategory.Q
    have hR := CommSq.mk (Functor.rightDerivedFunctor_map_Q_map_comp_objQIso_inv
      (ihomFunctor k₀ l X A) g)
    simp only [c, resolutionComparison_hom]
    exact (hC.vert_comp (hP.vert_comp hR)).w
  · intro A N _
    refine ⟨resolutionComparison A (DerivedCategory.kInjectiveRep N)
      (hi A (DerivedCategory.kInjectiveRep N)) ≪≫
        (ihomFunctor k₀ l X A).rightDerivedFunctor.mapIso
          (DerivedCategory.kInjectiveRepIso N).symm, ?_⟩
    intro hI
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
      ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
    rfl

end AlgebraicGeometry.ProEtaleWeilSheaf
